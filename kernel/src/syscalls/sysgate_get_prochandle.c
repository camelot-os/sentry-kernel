// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

stack_frame_t *gate_get_prochandle(stack_frame_t *frame, uint32_t job_label)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t job_handle;
    const task_meta_t *meta = NULL;
    uint8_t *svcexch;
    uint8_t current_domain;
    uint8_t job_domain;

    if (unlikely(mgr_task_get_handle(job_label, &job_handle) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_task_get_domain(current, &current_domain) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_task_get_domain(job_handle, &job_domain) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(current_domain != job_domain)) {
        /* domain mismatch, job handle is confodential to its current domain only */
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    /* set taskh_t value into svcexchange */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = task_get_svcexchange(meta);
    if (svcexch == NULL) {
        /* this should never happen! */
        panic(PANIC_CONFIGURATION_MISMATCH);
    }
    /*@ assert \valid(svcexch+(0..3)); */
    ((taskh_t*)svcexch)[0] = job_handle;
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
