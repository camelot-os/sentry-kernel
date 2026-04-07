// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

stack_frame_t *gate_yield(stack_frame_t *frame)
{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = frame;

    /*
     * In RMA policy, YIELDED is not significant, and thus is associated to READY
     * while YIELDED state is significant only in RMA scheduling mode, we yet prefer
     * to keep a common yield() syscall for all scheduling policies, as the yield() semantic is still
     * the same for all policies to reduce the formal demonstration complexity.
     */
    if (unlikely(mgr_task_set_state(current, JOB_STATE_YIELDED) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }

    next = sched_elect();
    if (unlikely(mgr_task_get_sp(next, &next_frame) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
    return next_frame;
}
