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
 * @def RRMQ task context for a given task
 *
 * @param active: set to true of the cell hold an active task
 * @param handler: taskh_t handler for current job
 * @param priority: task priority (bigger is higher)
 * @param quantum: task quantum, in ticker (HZ) multiple
 * @param state: task state, READY in active lists, may be other state in delayed
 */
typedef struct task_rrmq_state {
    taskh_t       handler;
    uint32_t      priority;
    uint32_t      quantum;    /**< set at spawn time to systick period */
    bool          active;
} task_rrmq_state_t;

/**
 * @def current task set for current time slot. Active while some task are eligible
 * RRMQ using two slotted task sets with flip/flopping, substitution comes when
 * no more job is elibible in current task set.
 * When a job has burn all its quantum, it is no more eligible for current slot
 */
typedef struct task_rrmq_jobset {
    uint32_t num_jobs;
    task_rrmq_state_t joblist[CONFIG_MAX_TASKS];
} task_rrmq_jobset_t;

/**
 * @brief Currentky ready tasks queue
 *
 * When a job is scheduled() it is added to the current active jobset.
 * When elected(), it is scheduled util it yield(), exit(), is blocked
 * by any external event or consumme all its quantum.
 * These event (yield syscall, ipc, systick handler, etc...) generate
 * a call to sched_elect(). This function is responsible for removing the
 * current task from the core, and returning another one.
 *
 * if:
 *  - systick sched subhandler rise: in that case, quantum is upgraded. If consumed:
 *     the job is pushed to other jobset
 *     the job quantum is refill
 *  - the job is blocked (blocking sycall), yield():
 *     the job is removed from the jobset
 *  - the job exit:
 *     the job is removed from jobset
 *
 * then the scheduler:
 *   elect another job of the current jobset respecting current RRM policy
 *     (Priority-based, queue based per priority selection)
 *   spawn systick with quantum timeout
 *   return the taskh_t to sched_elect() caller
 *
 * when there is no more job in current jobset, jobsets are switched.
 * If none of the queue hold an active job, clear the systick, and return idletask handle
 *   in that case, no more schedule-related interrupt will rise
 */
typedef struct sched_rrmq_context {
    task_rrmq_jobset_t    primary;         /**< jobset storage, first pool */
    task_rrmq_jobset_t    secondary;       /**< jobset storage, second pool */
    task_rrmq_jobset_t   *active_jobset;   /**< current jobset */
    task_rrmq_jobset_t   *backed_jobset;   /**< backed (next timeslot) jobset */
    task_rrmq_state_t    *current_job;     /**< current task that is being executed, or idle */
 } sched_rrmq_context_t;

static sched_rrmq_context_t
#ifndef __FRAMAC__
_Alignas(uint32_t)
#endif
sched_rrmq_ctx;

/**
 * Swapping current timeslot job set and backed job set. This happen when current
 * job set is empty. Any task that have been pushed back to the backed jobset
 * (yield or quantum fully consummed) is now eligible again, wrf. all elibible
 * task relative priorities.
 */
static inline void sched_swap_tables(void)
{
    if (sched_rrmq_ctx.active_jobset == &sched_rrmq_ctx.primary) {
        sched_rrmq_ctx.active_jobset = &sched_rrmq_ctx.secondary;
        sched_rrmq_ctx.backed_jobset = &sched_rrmq_ctx.primary;
    } else {
        sched_rrmq_ctx.active_jobset = &sched_rrmq_ctx.primary;
        sched_rrmq_ctx.backed_jobset = &sched_rrmq_ctx.secondary;
    }
}

kstatus_t sched_rrmq_init(void)
{
    pr_info("initialize RRMQ scheduler");
    memset(&sched_rrmq_ctx, 0x0, sizeof(sched_rrmq_context_t));
    pr_info("clear delay job list");
    sched_rrmq_ctx.active_jobset = &sched_rrmq_ctx.primary;
    sched_rrmq_ctx.backed_jobset = &sched_rrmq_ctx.secondary;
    return K_STATUS_OKAY;
}

static kstatus_t sched_rrmq_not_in_jobset(taskh_t t, task_rrmq_jobset_t *jobset)
{
    kstatus_t status = K_STATUS_OKAY;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (jobset->joblist[i].active == true) {
            if (jobset->joblist[i].handler == t) {
                status = K_ERROR_BADSTATE;
                break;
            }
        }
    }
    return status;
}

static kstatus_t sched_rrmq_add_to_jobset(taskh_t t, task_rrmq_jobset_t *jobset)
{
    kstatus_t status;
    job_state_t state;
    const task_meta_t *meta = NULL;
    uint8_t cell = 0;

    if (unlikely(jobset->num_jobs > CONFIG_MAX_TASKS)) {
        /* should never happen! */
        panic(PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG);
    }
    if (unlikely((status = mgr_task_get_metadata(t, &meta)) != K_STATUS_OKAY)) {
        pr_err("failed to get metadata for task %lx", t);
        goto err;
    }
    if (unlikely((status = mgr_task_get_state(t, &state)) != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((state != JOB_STATE_READY) && (state != JOB_STATE_YIELDED))) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    if (unlikely((status = sched_rrmq_not_in_jobset(t, jobset)) != K_STATUS_OKAY)) {
        goto err;
    }
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (jobset->joblist[i].active == false) {
            /* 1st empty cell, using it */
            cell = i;
            break;
        }
    }
    jobset->joblist[cell].handler = t;
    jobset->joblist[cell].priority = meta->priority;
    jobset->joblist[cell].quantum = meta->quantum;
    jobset->joblist[cell].active = true;
    jobset->num_jobs++;
    /* shedule is not an election, task job is only added to current taskset */
err:
    return status;
}




/* call context: SVC (sys_start) and systick(end of sleep - delayed)
 * This can also be called to awake another task that is blocked (end of sleep, or
 * ipc_wait from current task). The caller is responsible for updating the task
 * state properly using task manager API **before** calling scheduler.
 */
kstatus_t sched_rrmq_schedule(taskh_t t)
{
    kstatus_t status;
    status = sched_rrmq_add_to_jobset(t, sched_rrmq_ctx.active_jobset);
    return status;
}

/*
 * call context: SVC and systick. For SVC case: use task_mgr_set_state() first,
 * as the current task state may depend on the current syscall, and thus may
 * be delayed in consequence
 */
taskh_t sched_rrmq_elect(void)
{
    /* defaulting on idle */
    taskh_t tsk = mgr_task_get_idle();
    job_state_t state;
    if (unlikely(sched_rrmq_ctx.current_job == NULL)) {
        /* this case happen only when elect() is called by idle while there is
         * absolutely NO active job. This is an extreme case, where we
         * just recall idle.
         */
         goto elect;
    }
    if (unlikely(mgr_task_get_state(sched_rrmq_ctx.current_job->handler, &state) != K_STATUS_OKAY)) {
        pr_err("failed to get task state for task %x !",
           sched_rrmq_ctx.current_job->handler);
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if ((state == JOB_STATE_READY) || (state == JOB_STATE_YIELDED)) {
        /* task is not blocked (yield() maybe) and is still eligible, but
         * for next time slot, with a fresh quantum */
        /* not that in RRMQ policy, YIELDED is not significant, and thus is associated to READY */
        if (unlikely(state == JOB_STATE_YIELDED)) {
            if (unlikely(mgr_task_set_state(sched_rrmq_ctx.current_job->handler, JOB_STATE_READY) != K_STATUS_OKAY)) {
                panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
            }
        }
        sched_rrmq_add_to_jobset(sched_rrmq_ctx.current_job->handler, sched_rrmq_ctx.backed_jobset);
    } else {
        /* task is delayed, so removed from scheduler. sys_sleep() will typically use another
         * kernel component (a delay manager) to call the schedule() API at the good moment */
    }
    /* deactivate current from current slot */
    sched_rrmq_ctx.current_job->active = false;
    /* decrement current number of jobs in active jobset */
    sched_rrmq_ctx.active_jobset->num_jobs--;
elect:
    /* elect new task */
    /* if there is no more task in current set, switch */
    if (unlikely(sched_rrmq_ctx.active_jobset->num_jobs == 0)) {
        sched_swap_tables();
    }
    /* still no tasks ? schedule idle then */
    if (unlikely(sched_rrmq_ctx.active_jobset->num_jobs == 0)) {
        /* schedule idle */
        sched_rrmq_ctx.current_job = NULL;
        goto end;
    }
    /* there is at least one task eligible in current task set */
    /* RRM scheduling here */
    task_rrmq_state_t *next = NULL;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (sched_rrmq_ctx.active_jobset->joblist[i].active == true) {
            if (next == NULL) {
                next = &sched_rrmq_ctx.active_jobset->joblist[i];
            }
            if (sched_rrmq_ctx.active_jobset->joblist[i].priority > next->priority) {
                next = &sched_rrmq_ctx.active_jobset->joblist[i];
            }
        }
    }
    if (unlikely(next == NULL)) {
        sched_rrmq_ctx.current_job = NULL;
        goto end;
    }
    /* task found in list (priority based), elect it */
    sched_rrmq_ctx.current_job = next;
    tsk = next->handler;
end:
    return tsk;
}

taskh_t sched_rrmq_get_current(void)
{
    taskh_t tsk = mgr_task_get_idle();

    if (likely(sched_rrmq_ctx.current_job != NULL)) {
        tsk = sched_rrmq_ctx.current_job->handler;
    }

    return tsk;
}

/* call context: HW ticker IRQn */
stack_frame_t *sched_rrmq_refresh(stack_frame_t *frame)
{
    stack_frame_t *out_frame = frame;
    if (unlikely(sched_rrmq_ctx.current_job == NULL)) {
        /* no task as never been scheduled() nor elected() */
        goto end;
    }
    sched_rrmq_ctx.current_job->quantum--;
    if (unlikely(sched_rrmq_ctx.current_job->quantum == 0)) {
        /* quantum terminated: election required */
        taskh_t tsk = sched_rrmq_elect();
        /* context switching */
        if (unlikely(mgr_task_get_sp(tsk, &out_frame) != K_STATUS_OKAY)) {
            panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        }
    }
end:
    return out_frame;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t sched_rrmq_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif


/* default scheduler is RRMQ */

kstatus_t sched_schedule(taskh_t t) __attribute__((alias("sched_rrmq_schedule")));
taskh_t sched_elect(void) __attribute__((alias("sched_rrmq_elect")));
taskh_t sched_get_current(void) __attribute__((alias("sched_rrmq_get_current")));
kstatus_t sched_init(void) __attribute__((alias("sched_rrmq_init")));
stack_frame_t *sched_refresh(stack_frame_t *frame) __attribute__((alias("sched_rrmq_refresh")));
#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t sched_autotest(void) __attribute__((alias("sched_rrmq_autotest")));
#endif
