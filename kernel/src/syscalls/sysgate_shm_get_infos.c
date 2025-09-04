// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <uapi/types.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>
/** NOTE: memcpy impleted in Sentry zlib */
#include <string.h>

stack_frame_t *gate_shm_get_infos(stack_frame_t *frame, shmh_t shm)
{
    taskh_t current = sched_get_current();
    shm_user_t user;
    shm_infos_t shminfo = {0};
    secure_bool_t result;
    shm_infos_t *svcexch = NULL;
    const task_meta_t *meta;

    /*
     * to get back (ro) infos for a given SHM handle, the task need at least
     * one of SHM_OWN or SHM_USE
     */
    if (unlikely(
            mgr_security_has_capa(current, CAP_MEM_SHM_OWN) != SECURE_TRUE &&
            mgr_security_has_capa(current, CAP_MEM_SHM_USE) != SECURE_TRUE
        )) {
        pr_err("SHM ownership or user capability required");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    /*! NOTE: there is no need to check that the SHM handle exists, as the manager do that on its side */
    if (unlikely(mgr_mm_shm_get_task_type(shm, current, &user) != K_STATUS_OKAY)) {
        /* smoke test here, this branch should never happen */
        /*@ assert(false); */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* task is neither a user nor a owner declared in this SHM handle */
    if (unlikely(user == SHM_TSK_NONE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    shminfo.handle = shm;
    if (unlikely(mgr_mm_shm_get_label(shm, &shminfo.label) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_shm_get_baseaddr(shm, &shminfo.base) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_shm_get_size(shm, &shminfo.len) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_shm_is_mappable_by(shm, user, &result) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (result == SECURE_TRUE) {
        shminfo.perms |= SHM_PERMISSION_MAP;
    }
    if (unlikely(mgr_mm_shm_is_writeable_by(shm, user, &result) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (result == SECURE_TRUE) {
        shminfo.perms |= SHM_PERMISSION_WRITE;
    }
    /** TODO: transfer not yet supported */
    /* push back structure on the SVC_Exchange area */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (shm_infos_t*)meta->s_svcexchange;
    memcpy(svcexch, &shminfo, sizeof(shm_infos_t));
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
