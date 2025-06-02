// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>

#define CONFIG_MAX_DELAYED_EVENTS (CONFIG_MAX_TASKS)

/**
 * @def delay queue for task-related operations
 *
 * @param active: set to true of the cell hold an active task
 * @param handler: taskh_t handler for current job
 * @param type: type of delayed action : delayed job or delayed signal
 * @param pdata: u32 pdata that may need to be delayed (sigh_t or other type of delayed action)
 * @param wait_time_ms: time to wait in miliseconds
 */
typedef struct task_delay_state {
    taskh_t           handler;
    uint32_t          sig;
    uint32_t          wait_time_ms;
    uint32_t          remaining_time_ms;
    bool              periodic;
    bool              active;
} task_delay_state_t;

typedef struct delayed_jobset {
    task_delay_state_t joblist[CONFIG_MAX_TASKS];
    task_delay_state_t evlist[CONFIG_MAX_DELAYED_EVENTS];
} delayed_jobset_t;

#ifndef __FRAMAC__
static _Alignas(uint32_t)
#endif
delayed_jobset_t delay_ctx;

/**
 * @brief flush all events, events list is made empty
 */
kstatus_t mgr_time_delay_flush(void)
{
    memset(&delay_ctx, 0x0, sizeof(delayed_jobset_t));
    return K_STATUS_OKAY;
}

/**
 * @brief insert a new delayed job in the event queue
 *
 * @param job[in]: job identifier
 * @param delay_ms[in]: event duration in ms
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_BUSY if no remaining space found
 */
kstatus_t mgr_time_delay_add_job(taskh_t job, uint32_t delay_ms)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (delay_ctx.joblist[i].active == false) {
            delay_ctx.joblist[i].handler = job;
            delay_ctx.joblist[i].wait_time_ms = delay_ms;
            delay_ctx.joblist[i].remaining_time_ms = delay_ms;
            delay_ctx.joblist[i].active = true;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_BUSY;
end:
    return status;
}

/**
 * @brief remove a delayed job from the event queue
 *
 * @param job[in]: job identifier
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_NOENT if job not found in the delay queue
 */
kstatus_t mgr_time_delay_del_job(taskh_t job)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if ((delay_ctx.joblist[i].active == true) &&
            (delay_ctx.joblist[i].handler == job))
        {
            delay_ctx.joblist[i].active = false;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_NOENT;
end:
    return status;
}

/**
 * @brief insert a new signal in the event queue
 *
 * @param job[in]: job identifier
 * @param delay_ms[in]: event duration in ms
 * @param sig[in]: signal to postpone
 * @param periodic[in]: request a periodic alarm
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_BUSY if no remaining space found
 */
kstatus_t mgr_time_delay_add_signal(taskh_t job, uint32_t delay_ms, uint32_t sig, bool periodic)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_DELAYED_EVENTS; ++i) {
        if (delay_ctx.evlist[i].active == false) {
            delay_ctx.evlist[i].handler = job;
            delay_ctx.evlist[i].wait_time_ms = delay_ms;
            delay_ctx.evlist[i].remaining_time_ms = delay_ms;
            delay_ctx.evlist[i].sig = sig;
            delay_ctx.evlist[i].periodic = periodic;
            delay_ctx.evlist[i].active = true;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_BUSY;
end:
    return status;
}

/**
 * @brief remove a signal from the event queue, based on the job,delay tuple
 *
 * @param job[in]: job identifier
 * @param delay_ms[in]: delay_ms that was set at add time
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_NOENT if signal not found in the delay queue
 */
kstatus_t mgr_time_delay_del_signal(taskh_t job, uint32_t delay_ms)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if ((delay_ctx.evlist[i].active == true) &&
            (delay_ctx.evlist[i].handler == job) &&
            (delay_ctx.evlist[i].wait_time_ms == delay_ms))
        {
            delay_ctx.evlist[i].active = false;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_NOENT;
end:
    return status;
}

/**
 * @brief Delay mechanism ticker, to be called by hardware ticker (systick....)
 */
void mgr_time_delay_tick(void)
{
    job_state_t job_state;

    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (delay_ctx.joblist[i].active == true) {
            uint32_t num_ms = JIFFIES_TO_MSEC(1);
            if (likely(num_ms < delay_ctx.joblist[i].remaining_time_ms)) {
                delay_ctx.joblist[i].remaining_time_ms -= num_ms;
            } else {
                delay_ctx.joblist[i].remaining_time_ms = 0;

                mgr_task_get_state(delay_ctx.joblist[i].handler, &job_state);
                if (unlikely((job_state != JOB_STATE_SLEEPING)
                          && (job_state != JOB_STATE_SLEEPING_DEEP)
                          && (job_state != JOB_STATE_WAITFOREVENT))
                ) {
                    /*
                     * If we reach this point, this is a bug and the task was not
                     * removed from the delay joblist.
                     */
                    panic(PANIC_KERNEL_INVALID_MANAGER_STATE);
                }
                /* delay terminated for current delayed task */
                mgr_task_set_state(delay_ctx.joblist[i].handler, JOB_STATE_READY);
                mgr_task_set_sysreturn(delay_ctx.joblist[i].handler, STATUS_TIMEOUT);
                /* update previous NON SENSE status to OKAY now that the job is ready */
                sched_schedule(delay_ctx.joblist[i].handler);
                delay_ctx.joblist[i].active = false;
            }
        }
    }
    for (uint8_t i = 0; i < CONFIG_MAX_DELAYED_EVENTS; ++i) {
        if (delay_ctx.evlist[i].active == true) {
            uint32_t num_ms = JIFFIES_TO_MSEC(1);
            if (likely(num_ms < delay_ctx.evlist[i].remaining_time_ms)) {
                delay_ctx.evlist[i].remaining_time_ms -= num_ms;
            } else {
                delay_ctx.evlist[i].remaining_time_ms = 0;
                mgr_task_push_sig_event(delay_ctx.evlist[i].sig, delay_ctx.evlist[i].handler, delay_ctx.evlist[i].handler);
                if (delay_ctx.evlist[i].periodic == true) {
                    /* rearm event */
                    delay_ctx.evlist[i].remaining_time_ms = delay_ctx.evlist[i].wait_time_ms;
                } else {
                    /* clear event */
                    delay_ctx.evlist[i].active = false;
                }
            }
        }
    }
}
