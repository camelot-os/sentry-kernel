// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <uapi/types.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>

stack_frame_t *gate_shm_setcreds(stack_frame_t *frame, shmh_t shm, taskh_t target, SHMPermission perms)
{
    taskh_t current = sched_get_current();
    shmh_t shmhandle;
    shm_user_t user;
    shm_config_t config;
    secure_bool_t is_mapped = SECURE_TRUE;

    if (unlikely(mgr_security_has_capa(current, CAP_MEM_SHM_OWN) != SECURE_TRUE)) {
        pr_err("SHM ownership or user capability required");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_mm_shm_get_task_type(shm, current, &user) != K_STATUS_OKAY)) {
        /* smoke test here, this branch should never happen */
        /*@ assert(false); */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* is target exists ? */
    if (unlikely(mgr_task_handle_exists(target) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_NONE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_USER)) {
        /* only owner can set SHM creds */
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    mgr_mm_shm_is_mapped_by(shm, user, &is_mapped);
    if (unlikely(is_mapped == SECURE_TRUE)) {
        /* can't set creds for a user (or owner) that already have the SHM mapped */
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    /*@ assert (user == SHM_TSK_OWNER); */
    config.mappable = SECURE_FALSE;
    config.rw = SECURE_FALSE;
    config.transferable = SECURE_FALSE;

    if (perms & SHM_PERMISSION_MAP) {
        config.mappable = SECURE_TRUE;
    }
    if (perms & SHM_PERMISSION_WRITE) {
        config.rw = SECURE_TRUE;
    }
    if (perms & SHM_PERMISSION_TRANSFER) {
        config.transferable = SECURE_TRUE;
    }
    if (target == current) {
        /* settings own perms */
        mgr_mm_shm_configure(shm, SHM_TSK_OWNER, &config);
    } else {
        mgr_mm_shm_declare_user(shm, target);
        mgr_mm_shm_configure(shm, SHM_TSK_USER, &config);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
