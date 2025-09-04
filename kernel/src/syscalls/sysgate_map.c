// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi/uapi.h>
#include <sentry/syscalls.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/memory.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/sched.h>

/**
 * @fn gate_map_dev - Map a device in current task layout
 *
 * @param[in] frame current job's frame. Not updated here
 * @param[in] device device handle to map
 *
 * @return current job frame (no modification)
 */
stack_frame_t *gate_map_dev(stack_frame_t *frame, devh_t device)
{
    taskh_t current = sched_get_current();
    taskh_t task;
    uint32_t capa;
    secure_bool_t is_mapped;
    secure_bool_t is_configured;

    if (unlikely(mgr_device_get_owner(device, &task) != K_STATUS_OKAY)) {
        pr_err("failed to find owner!");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* device is valid */
    if (unlikely(current != task)) {
        pr_err("you are not owner!");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely((capa = mgr_device_get_capa(device)) == 0)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_security_has_capa(current, capa) != SECURE_TRUE)) {
        pr_err("you need capa!");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    /* current task own the device and has capa to use it */

    if (mgr_device_get_map_state(device, &is_mapped) != K_STATUS_OKAY) {
        /* should not happen with a valid device */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(is_mapped != SECURE_FALSE)) {
        /* invstate ? */
        pr_err("already map ?");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (mgr_device_get_configured_state(device, &is_configured) != K_STATUS_OKAY) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (likely(is_configured == SECURE_FALSE)) {
        mgr_device_configure(device);
    }
    if (unlikely(mgr_mm_map_device(current, device) != K_STATUS_OKAY)) {
        pr_err("map failed!");
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    pr_debug("mapping device %x for task %x", device, current);
    mgr_device_set_map_state(device, SECURE_TRUE);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}


stack_frame_t *gate_unmap_dev(stack_frame_t *frame, devh_t device)
{
    taskh_t current = sched_get_current();
    taskh_t task;
    uint32_t capa;
    secure_bool_t is_mapped;

    if (unlikely(mgr_device_get_owner(device, &task) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* device is valid */
    if (unlikely(current != task)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely((capa = mgr_device_get_capa(device)) == 0)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_security_has_capa(current, capa) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    /* current task own the device and has capa to use it */

    if (mgr_device_get_map_state(device, &is_mapped) != K_STATUS_OKAY) {
        /* should not happen with a valid device */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(is_mapped != SECURE_TRUE)) {
        /* invstate ? */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_unmap_device(current, device) != K_STATUS_OKAY)) {
        /* should not happen with a valid, mapped and owned device */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    mgr_device_set_map_state(device, SECURE_FALSE);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}

/**
 * @fn gate_map_dev - Map a device in current task layout
 *
 * @param[in] frame current job's frame. Not updated here
 * @param[in] device device handle to map
 *
 * @return current job frame (no modification)
 */
stack_frame_t *gate_map_shm(stack_frame_t *frame, shmh_t shm)
{
    taskh_t current = sched_get_current();
    kstatus_t status;
    shm_user_t user;

    if (unlikely(mgr_security_has_capa(current, CAP_MEM_SHM_USE) != SECURE_TRUE)) {
        pr_err("SHM use capability required");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    status = mgr_mm_shm_get_task_type(shm, current, &user);
    if (unlikely(status != K_STATUS_OKAY)) {
        /* shm is invalid */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_NONE)) {
        /* shm is not accessible for current */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* current task is an owner or user of the shm */
    if (unlikely((status = mgr_mm_map_shm(current, shm)) != K_STATUS_OKAY)) {
        /* already mapped or memory backend error */
        switch (status) {
            case K_ERROR_INVPARAM:
                mgr_task_set_sysreturn(current, STATUS_NO_ENTITY);
                break;
            case K_ERROR_BADSTATE:
                mgr_task_set_sysreturn(current, STATUS_ALREADY_MAPPED);
                break;
            case K_ERROR_DENIED:
                mgr_task_set_sysreturn(current, STATUS_DENIED);
                break;
            default:
                mgr_task_set_sysreturn(current, STATUS_BUSY);
        }
        goto end;
    }
    pr_debug("mapping shm %x for task %x", shm, current);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}

stack_frame_t *gate_unmap_shm(stack_frame_t *frame, shmh_t shm)
{
    kstatus_t status;
    taskh_t current = sched_get_current();
    secure_bool_t is_mapped;
    shm_user_t user;

    /* note: no creds check at umap() time, as creds are verified at map() time */
    status = mgr_mm_shm_get_task_type(shm, current, &user);
    if (unlikely(status != K_STATUS_OKAY)) {
        /* shm is invalid */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_NONE)) {
        /* shm is not accessible for current */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (mgr_mm_shm_is_mapped_by(shm, user, &is_mapped) != K_STATUS_OKAY) {
        /* should not happen with a valid shm */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(is_mapped != SECURE_TRUE)) {
        /* not mapped, and thus can't be unmapped */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_unmap_shm(current, shm) != K_STATUS_OKAY)) {
        /* should not happen with a valid, mapped and accessible shm */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    pr_debug("unmapping shm %x for task %x", shm, current);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
