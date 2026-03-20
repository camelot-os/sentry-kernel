// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <string.h>
#include <sentry/arch/asm-generic/panic.h>
#include <uapi/handle.h>
#include <sentry/ktypes.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>

/**
 * @brief Rate Monotonic Algorithm (RMA) scheduler
 *
 * Classical fixed-priority preemptive scheduling policy where each task is
 * assigned a static priority inversely proportional to its period.
 *
 * The task period is taken from the @c priority field of the task metadata
 * structure: a smaller value means a shorter period and therefore a higher
 * scheduling priority.  The @c quantum field is not used by this scheduler.
 *
 * At each HW-ticker tick (sched_refresh), every active task's remaining
 * counter is decremented.  When a counter reaches zero the task starts a new
 * activation period: the counter is reset to the task period and, if the task
 * is not currently blocked, it is marked ready.  If the newly activated task
 * has a higher priority (smaller period) than the task currently running,
 * a preemption is triggered.
 *
 * At election time (sched_elect), the ready task with the smallest period is
 * selected.  A task that yields while in JOB_STATE_READY remains eligible (it
 * keeps its ready flag) so that the priority ordering is preserved across
 * voluntary yield calls; only a blocking syscall (sleep, IPC wait, …) removes
 * the task from the ready set until it is re-activated via sched_schedule.
 */

/**
 * @brief Per-task RMA scheduler state
 *
 * @param handler   task handle registered with the scheduler
 * @param period    task period in ticks, taken from meta->priority (never 0)
 * @param remaining ticks remaining until the next period activation
 * @param active    true when this slot holds a registered task
 * @param ready     true when the task is eligible to be elected
 */
typedef struct task_rma_state {
    taskh_t  handler;
    uint32_t period;
    uint32_t remaining;
    bool     active;
    bool     ready;
} task_rma_state_t;

/**
 * @brief RMA scheduler global context
 *
 * @param jobs        flat array of all registered tasks
 * @param current_job pointer to the slot of the task currently executing,
 *                    NULL when the idle task is running
 */
typedef struct sched_rma_context {
    task_rma_state_t  jobs[CONFIG_MAX_TASKS];
    task_rma_state_t *current_job;
} sched_rma_context_t;

static sched_rma_context_t sched_rma_ctx;

kstatus_t sched_rma_init(void)
{
    pr_info("initialize RMA scheduler");
    memset(&sched_rma_ctx, 0x0, sizeof(sched_rma_context_t));
    return K_STATUS_OKAY;
}

/**
 * @brief Find the slot index holding task @p t.
 *
 * @return index in [0, CONFIG_MAX_TASKS) when found, CONFIG_MAX_TASKS otherwise
 */
static inline uint8_t sched_rma_find_slot(taskh_t t)
{
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (sched_rma_ctx.jobs[i].active && sched_rma_ctx.jobs[i].handler == t) {
            return i;
        }
    }
    return CONFIG_MAX_TASKS;
}

/**
 * @brief Add a task to the RMA scheduler or re-activate it after unblocking.
 *
 * First call (task not yet tracked): the task is inserted into the first free
 * slot; its period is read from meta->priority and its activation counter is
 * initialised to the period value so that it becomes eligible immediately.
 *
 * Subsequent calls (task returning after a blocking syscall): the existing
 * slot is simply marked ready so the task re-enters the election pool.
 *
 * call context: SVC (sys_start) and any unblocking path (end of sleep,
 *               IPC/signal wakeup, …)
 */
kstatus_t sched_rma_schedule(taskh_t t)
{
    kstatus_t status = K_STATUS_OKAY;
    const task_meta_t *meta = NULL;
    uint8_t slot;

    /* task already tracked: re-enable for its current/next period */
    slot = sched_rma_find_slot(t);
    if (slot < CONFIG_MAX_TASKS) {
        sched_rma_ctx.jobs[slot].ready = true;
        goto end;
    }

    /* new task: find a free slot */
    slot = CONFIG_MAX_TASKS;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (!sched_rma_ctx.jobs[i].active) {
            slot = i;
            break;
        }
    }
    if (unlikely(slot == CONFIG_MAX_TASKS)) {
        panic(PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG);
    }

    if (unlikely((status = mgr_task_get_metadata(t, &meta)) != K_STATUS_OKAY)) {
        pr_err("failed to get metadata for task %lx", t);
        goto end;
    }
    if (unlikely(meta->priority == 0)) {
        pr_err("task %lx has period 0, invalid for RMA", t);
        status = K_ERROR_INVPARAM;
        goto end;
    }

    sched_rma_ctx.jobs[slot].handler   = t;
    sched_rma_ctx.jobs[slot].period    = (uint32_t)meta->priority;
    sched_rma_ctx.jobs[slot].remaining = (uint32_t)meta->priority;
    sched_rma_ctx.jobs[slot].active    = true;
    sched_rma_ctx.jobs[slot].ready     = true;
end:
    return status;
}

/**
 * @brief Elect the next task to run following the RMA policy.
 *
 * The ready task with the smallest period (highest frequency, highest RMA
 * priority) is selected.  The current task:
 *
 *   - remains in the ready set when its state is JOB_STATE_READY (voluntary
 *     yield or preemption): it keeps competing at its original priority;
 *   - is removed from the ready set when its state differs from
 *     JOB_STATE_READY (blocking syscall): sched_schedule() will re-activate
 *     it when the blocking condition is resolved.
 *
 * If no task is ready the idle task handle is returned.
 *
 * call context: SVC and systick handler
 */
taskh_t sched_rma_elect(void)
{
    taskh_t tsk = mgr_task_get_idle();
    job_state_t state;

    if (likely(sched_rma_ctx.current_job != NULL)) {
        if (unlikely(mgr_task_get_state(sched_rma_ctx.current_job->handler, &state) != K_STATUS_OKAY)) {
            pr_err("failed to get task state for task %x!",
                   sched_rma_ctx.current_job->handler);
            panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        }
        if (state == JOB_STATE_READY) {
            /* voluntary yield or preemption: task remains ready for re-election */
            sched_rma_ctx.current_job->ready = true;
        } else {
            /* blocking syscall: remove from ready set until sched_schedule
             * re-activates the task */
            sched_rma_ctx.current_job->ready = false;
        }
        sched_rma_ctx.current_job = NULL;
    }

    /* elect: ready task with the smallest period (= highest RMA priority) */
    task_rma_state_t *next = NULL;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (sched_rma_ctx.jobs[i].active && sched_rma_ctx.jobs[i].ready) {
            if (next == NULL || sched_rma_ctx.jobs[i].period < next->period) {
                next = &sched_rma_ctx.jobs[i];
            }
        }
    }

    if (next != NULL) {
        sched_rma_ctx.current_job = next;
        tsk = next->handler;
    }

    return tsk;
}

taskh_t sched_rma_get_current(void)
{
    taskh_t tsk = mgr_task_get_idle();

    if (likely(sched_rma_ctx.current_job != NULL)) {
        tsk = sched_rma_ctx.current_job->handler;
    }

    return tsk;
}

/**
 * @brief Per-tick RMA period management: update counters and preempt if needed.
 *
 * For each registered task the remaining counter is decremented.  When it
 * reaches zero:
 *   - the counter is reset to the task period (new activation);
 *   - the task is marked ready if it is not currently blocked
 *     (JOB_STATE_READY), so that a blocked task only re-enters the ready set
 *     through the sched_schedule() path (called at unblock time);
 *   - if the newly activated task is not the currently running task and has a
 *     smaller period (higher priority), preemption is requested.
 *
 * call context: HW ticker IRQn
 */
stack_frame_t *sched_rma_refresh(stack_frame_t *frame)
{
    stack_frame_t *out_frame = frame;
    bool need_elect = false;

    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (!sched_rma_ctx.jobs[i].active) {
            continue;
        }

        if (sched_rma_ctx.jobs[i].remaining > 0) {
            sched_rma_ctx.jobs[i].remaining--;
        }

        if (sched_rma_ctx.jobs[i].remaining == 0) {
            /* new activation period */
            sched_rma_ctx.jobs[i].remaining = sched_rma_ctx.jobs[i].period;

            job_state_t state;
            if (likely(mgr_task_get_state(sched_rma_ctx.jobs[i].handler, &state) == K_STATUS_OKAY)) {
                if (state == JOB_STATE_READY) {
                    sched_rma_ctx.jobs[i].ready = true;
                }
                /* if blocked, sched_schedule() will mark ready on wakeup */
            }

            /* check if this task should preempt the currently running one */
            if (sched_rma_ctx.jobs[i].ready &&
                &sched_rma_ctx.jobs[i] != sched_rma_ctx.current_job) {
                if (sched_rma_ctx.current_job == NULL ||
                    sched_rma_ctx.jobs[i].period < sched_rma_ctx.current_job->period) {
                    need_elect = true;
                }
            }
        }
    }

    if (unlikely(need_elect)) {
        taskh_t tsk = sched_rma_elect();
        if (unlikely(mgr_task_get_sp(tsk, &out_frame) != K_STATUS_OKAY)) {
            panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        }
    }

    return out_frame;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t sched_rma_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

/*
 * Public API aliases — the single scheduler model selects exactly one
 * implementation at build time through Kconfig; these aliases bind the generic
 * sched_* symbols to the RMA-specific implementations when CONFIG_SCHED_RMA
 * is active.
 */
kstatus_t sched_schedule(taskh_t t) __attribute__((alias("sched_rma_schedule")));
taskh_t sched_elect(void) __attribute__((alias("sched_rma_elect")));
taskh_t sched_get_current(void) __attribute__((alias("sched_rma_get_current")));
kstatus_t sched_init(void) __attribute__((alias("sched_rma_init")));
stack_frame_t *sched_refresh(stack_frame_t *frame) __attribute__((alias("sched_rma_refresh")));
#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t sched_autotest(void) __attribute__((alias("sched_rma_autotest")));
#endif
