// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/device.h>
#include <sentry/sched.h>

#include <sentry/arch/asm-generic/panic.h>


stack_frame_t *gate_get_devhandle(stack_frame_t *frame, uint8_t devid)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t devowner;
    devh_t devhandle;
    const task_meta_t *meta;
    uint32_t *svcexch;

    if (unlikely(mgr_device_get_devhandle(devid, &devhandle) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_device_get_owner(devhandle, &devowner) != K_STATUS_OKAY)) {
        /* smoke test here, this branch should never happen */
        /*@ assert(false); */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(devowner != current)) {
        /**
         * INFO: do not declare a different return type on ownership check error to
         * avoid the ability to list all other devices id by sequential calls with
         * DENIED return
         */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* set devh_t value into svcexchange */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint32_t*)meta->s_svcexchange;
    svcexch[0] = devhandle;
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
