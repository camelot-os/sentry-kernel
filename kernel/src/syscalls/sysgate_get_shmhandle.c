// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>


stack_frame_t *gate_get_shmhandle(stack_frame_t *frame, uint32_t shmid)
{
    taskh_t current = sched_get_current();
    shmh_t shmhandle;
    shm_user_t user;
    const task_meta_t *meta;
    uint32_t *svcexch;

    if (unlikely(mgr_security_has_capa(current, CAP_MEM_SHM_OWN) != SECURE_TRUE)) {
        pr_err("SHM ownership capability required");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_mm_shm_get_handle(shmid, &shmhandle) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_shm_get_task_type(shmhandle, current, &user) != K_STATUS_OKAY)) {
        /* smoke test here, this branch should never happen */
        /*@ assert(false); */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_NONE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* set shmh_t value into svcexchange */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint32_t*)meta->s_svcexchange;
    svcexch[0] = shmhandle;
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
