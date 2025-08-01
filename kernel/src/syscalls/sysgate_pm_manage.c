// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/security.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/sched.h>

stack_frame_t *gate_pm_manage(stack_frame_t *frame, uint32_t pm_command)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;

    if (unlikely(mgr_security_has_capa(current, CAP_SYS_POWER) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(pm_command > CPU_SLEEP_ALLOW_SLEEP)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(
        (pm_command <= CPU_SLEEP_WAIT_FOR_EVENT) &&
        (mgr_task_is_idletask(current) != SECURE_TRUE)
    )) {
        /* only idle can request entering wait for event/interrupt CPU states */
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    switch (pm_command) {
        case CPU_SLEEP_WAIT_FOR_EVENT:
            __WFE();
            break;
        case CPU_SLEEP_WAIT_FOR_INTERRUPT:
            __WFI();
            break;
        default:
            /** TODO: support for PM (un)lock */
            break;
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
