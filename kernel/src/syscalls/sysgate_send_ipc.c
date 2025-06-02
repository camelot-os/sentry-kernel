// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/sched.h>
#include <sentry/arch/asm-generic/panic.h>


/*
 * direct and indirect deadlock detection
 */
typedef struct deadlock_check_frame {
    taskh_t peer;
    uint8_t idx;
} deadlock_check_frame_t;

/**
 * @fn iterative (stack based) implementation of direct and indirect deadlock detection.
 *
 * The kernel check that when emitting an IPC to a given target, this do not generate
 * an IPC deadlock, with a direct (1 step) or indirect (multisteps) path.
 * Deadlock happen if the ipc emission chain is a closed path.
 */
secure_bool_t ipc_generates_deadlock(taskh_t current, taskh_t target)
{
    secure_bool_t result = SECURE_TRUE;
    kstatus_t status;
    taskh_t peer;
    taskh_t next_peer;
    deadlock_check_frame_t stack[CONFIG_MAX_TASKS];
    int stack_top = -1;

    // Initialize the stack with the initial state
    stack[++stack_top] = (deadlock_check_frame_t){current, 0};

    while (stack_top >= 0) {
        deadlock_check_frame_t *frame = &stack[stack_top];
        peer = frame->peer;

        // Iterate through the peers
        status = mgr_task_local_ipc_iterate(peer, &next_peer, &frame->idx);
        if (unlikely(status == K_STATUS_OKAY)) {
            /* peer have an IPC input from next_peer, checking him */
            if (next_peer == target) {
                /* deadlock found */
                goto deadlock;
            } else {
                /* next peer is not initial target. Do it as input IPCs from
                 * someone else ?
                 */
                if ((stack_top + 1) >= CONFIG_MAX_TASKS) {
                    /* this MUST not happen: the IPC chain is bigger that
                     * the effective number of task !!!
                     */
                     panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
                }
                stack[++stack_top] = (deadlock_check_frame_t){next_peer, 0};
            }
        } else {
            /* No IPC input found for that peer, unstack context */
            --stack_top;
        }
    }
    result = SECURE_FALSE;
deadlock:
    return result;
}

stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    taskh_t next;
    job_state_t dest_state;
    /* sanitize first */
    if (unlikely(len > (CONFIG_SVC_EXCHANGE_AREA_LEN - sizeof(exchange_event_t)))) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto err;
    }
    /*
     * if emitting IPC generates a direct (current <-> target) or indirect
     * (current -> target -> any_others -> current) deadlock, this syscall
     * must not initiate an IPC and return STATUS_DEADLK instead.
     */
    if (unlikely(ipc_generates_deadlock(current, target) == SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DEADLK);
        goto err;
    }
    if (unlikely(mgr_task_handle_exists(target) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto err;
    }
    /* TODO: deadlock detecion */

    /* push IPC event to target */
    if (unlikely(mgr_task_push_ipc_event(len, current, target) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto err;
    }
    /* except in autotest mode, a job can't send a message to itself */
    if (unlikely(current == target)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto err_autotest;
    }
    /* lock current job */
    mgr_task_set_state(current, JOB_STATE_IPC_SEND_BLOCKED);
    /* as IPC return call is asynchronously set, set NON_SENSE as default */
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
    /* check if target can be sheduled again */
    mgr_task_get_state(target, &dest_state);
    if ((dest_state == JOB_STATE_SLEEPING) ||
        (dest_state == JOB_STATE_WAITFOREVENT)) {
        /* if the job exists in the delay queue (sleep or waitforevent with timeout)
         * remove it from the delay queue before schedule
         * TODO: use a dedicated state (WAITFOREVENT_TIMEOUT) to call this
         * function only if needed
         */
        mgr_time_delay_del_job(target);
        mgr_task_set_sysreturn(target, STATUS_INTR);
        mgr_task_set_state(target, JOB_STATE_READY);
        sched_schedule(target);
    }
    next = sched_elect();
    if (unlikely(mgr_task_get_sp(next, &next_frame) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
err_autotest:
#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* autotest special case: if sending to itself, set current as ready,
     * no schedule neither elect has been made
     */
    if (unlikely(current == target)) {
        mgr_task_set_sysreturn(current, STATUS_OK);
    }
#endif
err:
    return next_frame;
}
