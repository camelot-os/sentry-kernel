// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry memory manager implementation
 */
#include <inttypes.h>

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/arch/asm-generic/panic.h>


#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/mpu.h>
#include <sentry/arch/asm-cortex-m/handler.h>
#elif defined(__x86_64__)
// TODO add core,mmu and handler headers (or minimum to compile)
#elif defined(__i386__)
// TODO add core,mmu and handler headers (or minimum to compile)
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/pmp.h>
#include <sentry/arch/asm-rv32/handler.h>
#include <sentry/arch/asm-generic/platform.h>
#else
#error "unsupported architecture!"
#endif

#include <sentry/managers/debug.h>
#include <sentry/managers/device.h>
#include <sentry/managers/task.h>
#include <uapi/handle.h>

#include <sentry/managers/memory.h>
#include "memory.h"

extern uint32_t _svtor;
extern uint32_t _ram_start;


static secure_bool_t mm_configured;



secure_bool_t mgr_mm_configured(void)
{
    if (mm_configured == SECURE_TRUE) {
        return mm_configured;
    }
    return SECURE_FALSE;
}

/*
 * Per region function implementation, forced inline, but
 * clearer.
 */
/*@
    assigns (*(MPU_Type*)MPU_BASE);
    ensures \result == K_STATUS_OKAY;
 */
__STATIC_INLINE kstatus_t mgr_mm_map_kernel_txt(void)
{
    kstatus_t status = K_STATUS_OKAY;
    struct mpu_region_desc kernel_txt_config = {
        .id = MM_REGION_KERNEL_TXT,
        .addr = (uint32_t)&_svtor, /* starting at vtor for ^2 size vs base alignment */
        .size = MPU_REGION_SIZE_32KB,
        .access_perm = MPU_REGION_PERM_PRIV_RO,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = false,
        .shareable = false,
    };
    status = mpu_load_descriptors(&kernel_txt_config, 1);
    /*@ assert (status == K_STATUS_OKAY); */
    return status;
}

/*@
    assigns (*(MPU_Type*)MPU_BASE);
    ensures \result == K_STATUS_OKAY;
 */
__STATIC_INLINE kstatus_t mgr_mm_map_kernel_data(void)
{
    kstatus_t status = K_STATUS_OKAY;
    struct mpu_region_desc kernel_data_config = {
        .id = MM_REGION_KERNEL_DATA,
        .addr = (uint32_t)&_ram_start,
        .size = MPU_REGION_SIZE_16KB, /* ldscript to fix, this is big */
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = true,
        .shareable = false,
    };
    status = mpu_load_descriptors(&kernel_data_config, 1);
    /*@ assert (status == K_STATUS_OKAY); */
    return status;
}

/**
 * Reduce current data section to svcexchange only
 * INFO: optimisation can be done here: MPU register states should be cached in task data to avoid dyn calculation
 */
kstatus_t mgr_mm_resize_taskdata_to_svcexchange(taskh_t target)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_meta_t const * meta;
    if (unlikely((status = mgr_task_get_metadata(target, &meta)) == K_ERROR_INVPARAM)) {
        /* invalid task handle */
        pr_err("failed to get metadata for task %08x", target);
        goto err;
    }
    struct mpu_region_desc user_data_config = {
        .id = MM_REGION_TASK_DATA,
        .addr = (uint32_t)meta->s_svcexchange, /* To define: where start the task RAM ? .data ? other ? */
        .size = mpu_convert_size_to_region(CONFIG_SVC_EXCHANGE_AREA_LEN),
        .access_perm = MPU_REGION_PERM_FULL,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = true,
        .shareable = false,
    };
    status = mpu_load_descriptors(&user_data_config, 1);
err:
    return status;
}


/*@
    assigns (*(MPU_Type*)MPU_BASE);
 */
kstatus_t mgr_mm_map_task(taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const layout_resource_t *layout;
    if (unlikely((status = mgr_task_get_layout_from_handle(t, &layout)) != K_STATUS_OKAY)) {
        pr_err("failed to get meta for task handle %x", t);
        goto err;
    }
    mpu_fastload(MM_REGION_TASK_TXT, layout, TASK_MAX_RESSOURCES_NUM);
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * Map the svc exchange area of a given task, using the kernel dev slot
 */
kstatus_t mgr_mm_map_svcexchange(taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (mgr_mm_configured() == SECURE_TRUE) {
        const task_meta_t *meta;
        if (unlikely(mgr_task_get_metadata(t, &meta) != K_STATUS_OKAY)) {
            goto err;
        }
        struct mpu_region_desc svcexch_config = {
            .id = MM_REGION_KERNEL_DEVICE,
            .addr = meta->s_svcexchange,
            .size = mpu_convert_size_to_region(CONFIG_SVC_EXCHANGE_AREA_LEN),
            .access_perm = MPU_REGION_PERM_PRIV,
            .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
            .mask = 0x0,
            .noexec = true,
            .shareable = false,
        };
        pr_debug("mapping %x, size %u", meta->s_svcexchange, CONFIG_SVC_EXCHANGE_AREA_LEN);
        status = mpu_load_descriptors(&svcexch_config, 1);
    }
err:
    return status;
}

kstatus_t mgr_mm_unmap_device(taskh_t tsk, devh_t dev)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const devinfo_t *devinfo;
    layout_resource_t layout;
    const layout_resource_t *layout_tab;
    uint8_t id;

    if (unlikely((status = mgr_device_get_info(dev, &devinfo)) != K_STATUS_OKAY)) {
        pr_err("failed to get device meta from dev handle %x", dev);
        goto err;
    }
    if (unlikely((status = mgr_task_get_layout_from_handle(tsk, &layout_tab)) != K_STATUS_OKAY)) {
        pr_err("failed to get task ressource layout from task handle %x", tsk);
        goto err;
    }
    if (unlikely((status = mpu_get_id_from_address(layout_tab, TASK_MAX_RESSOURCES_NUM, (uint32_t)devinfo->baseaddr, &id)) != K_STATUS_OKAY)) {
        pr_err("device %x not found in mapped layout", dev);
        goto err;
    }
    status = mgr_task_remove_resource(tsk, mgr_mm_region_to_layout_id(id));
err:
    return status;
}

kstatus_t mgr_mm_map_device(taskh_t tsk, devh_t dev)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const devinfo_t *devinfo;
    struct mpu_region_desc mpu_cfg;
    layout_resource_t layout;
    const layout_resource_t *layout_tab;

    if (unlikely((status = mgr_device_get_info(dev, &devinfo)) != K_STATUS_OKAY)) {
        pr_err("failed to get device meta from dev handle %x", dev);
        goto err;
    }
    if (unlikely((status = mgr_task_get_layout_from_handle(tsk, &layout_tab)) != K_STATUS_OKAY)) {
        pr_err("failed to get task ressource layout from task handle %x", tsk);
        goto err;
    }
    /**
     * NOTE: here, we ask for the first empty field in task layout.
     * This field id must be incremented of 2 (<<1) as the first region of th layout_tab
     * correspond to region 2 (see kernel and task memory mapping) as the kernel has locked
     * regions 0 and 1 for itself.
     */
    if (unlikely((status = mpu_get_free_id(layout_tab, TASK_MAX_RESSOURCES_NUM, &mpu_cfg.id)) != K_STATUS_OKAY)) {
        pr_err("no free slot to map device");
        status = K_ERROR_BUSY;
        goto err;
    }
#if ! MPU_FASTLOAD_ALIGNED
    /* in MPU that allow block-mapping from any region number, the region number is based
     * on the id field, while in the other case, it is set separatedly */
    /** FIXME: this fix should be fully invisible here and being instead managed in mpu
     * arch-specific backend, such as pmsav7 vs pmsav8 */
    mpu_cfg.id += 2; /* as layout starts at task TXT, defined as reg 2, it must be incremented */
#endif
    mpu_cfg.addr = (uint32_t)devinfo->baseaddr;
    mpu_cfg.size = mpu_convert_size_to_region(devinfo->size);
    mpu_cfg.access_perm = MPU_REGION_PERM_FULL; /* RW for priv+user */
    mpu_cfg.access_attrs = MPU_REGION_ATTRS_DEVICE;
    mpu_cfg.mask = 0x0;
    mpu_cfg.noexec = true;
    mpu_cfg.shareable = false;
    status = mpu_forge_resource(&mpu_cfg, &layout);
    /*@ assert status == K_STATUS_OKAY; */

    status = mgr_task_add_resource(tsk, mpu_cfg.id, layout);
    if (unlikely(status != K_STATUS_OKAY)) {
        /* should not happen as already checked when getting free id */
        /*@ assert false; */
        pr_err("no free slot to map device");
        status = K_ERROR_BUSY;
        goto err;
    }
    /*@ assert status == K_STATUS_OKAY; */
err:
    return status;
}


kstatus_t mgr_mm_map_shm(taskh_t tsk, shmh_t shm)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const shm_meta_t *shm_meta;
    struct mpu_region_desc mpu_cfg;
    layout_resource_t layout;
    const layout_resource_t *layout_tab;
    secure_bool_t result;
    shm_user_t user;

    if (unlikely((status = mgr_mm_shm_get_meta(shm, &shm_meta)) != K_STATUS_OKAY)) {
        goto err;
    }
    status = mgr_mm_shm_get_task_type(shm, tsk, &user);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    status = mgr_mm_shm_is_mappable_by(shm, user, &result);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    /*@ assert (status == K_STATUS_OKAY); */
    if (unlikely(result == SECURE_FALSE)) {
        /* this SHM is not mappable ! */
        status = K_ERROR_DENIED;
        goto err;
    }
    /* detect if tsk is owner or user. must not fail */
    status = mgr_mm_shm_get_task_type(shm, tsk, &user);
    /*@ assert (status == K_STATUS_OKAY); */
    if (unlikely(user == SHM_TSK_NONE)) {
        goto err;
    }
    /* now that we know who is requesting, check user-related flags */
    status = mgr_mm_shm_is_mapped_by(shm, user, &result);
    /*@ assert (result == K_STATUS_OKAY); */
    if (result == SECURE_TRUE) {
        /* already mapped ! */
        status = K_ERROR_BADSTATE;
        goto err;
    }
    if (unlikely((status = mgr_task_get_layout_from_handle(tsk, &layout_tab)) != K_STATUS_OKAY)) {
        goto err;
    }
    /**
     * NOTE: here, we ask for the first empty field in task layout.
     * This field id must be incremented of 2 (<<1) as the first region of th layout_tab
     * correspond to region 2 (see kernel and task memory mapping) as the kernel has locked
     * regions 0 and 1 for itself.
     */
    if (unlikely((status = mpu_get_free_id(layout_tab, TASK_MAX_RESSOURCES_NUM, &mpu_cfg.id)) != K_STATUS_OKAY)) {
        status = K_ERROR_BUSY;
        goto err;
    }

#if ! MPU_FASTLOAD_ALIGNED
    /* in MPU that allow block-mapping from any region number, the region number is based
     * on the id field, while in the other case, it is set separatedly */
    /** FIXME: this fix should be fully invisible here and being instead managed in mpu
     * arch-specific backend, such as pmsav7 vs pmsav8 */
    mpu_cfg.id += 2; /* as layout starts at task TXT, defined as reg2, it must be incremented */
#endif
    mpu_cfg.addr = (uint32_t)shm_meta->baseaddr;
    mpu_cfg.size = mpu_convert_size_to_region(shm_meta->size);

    /* used writeable flags declared in config */
    if (unlikely((status = mgr_mm_shm_is_writeable_by(shm, user, &result)) != K_STATUS_OKAY)) {
        goto err;
    }
    if (result == SECURE_TRUE) {
        mpu_cfg.access_perm = MPU_REGION_PERM_FULL; /* RW for priv+user */
    } else {
        mpu_cfg.access_perm = MPU_REGION_PERM_RO; /* RO for priv+user */
    }
    mpu_cfg.access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE;
    mpu_cfg.mask = 0x0;
    mpu_cfg.noexec = true;
    mpu_cfg.shareable = false;
    status = mpu_forge_resource(&mpu_cfg, &layout);
    /*@ assert status == K_STATUS_OKAY; */
    status = mgr_task_add_resource(tsk, mpu_cfg.id, layout);
    if (unlikely(status != K_STATUS_OKAY)) {
        /* should not happen as already checked when getting free id */
        /*@ assert false; */
        status = K_ERROR_BUSY;
        goto err;
    }
    status = mgr_mm_shm_set_mapflag(shm, user, SECURE_TRUE);
    /*@ assert status == K_STATUS_OKAY; */
err:
    return status;
}

kstatus_t mgr_mm_unmap_shm(taskh_t tsk, shmh_t shm)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const shm_meta_t *shm_meta;
    layout_resource_t layout;
    const layout_resource_t *layout_tab;
    secure_bool_t result;
    shm_user_t user;
    uint8_t id;

    if (unlikely((status = mgr_mm_shm_get_meta(shm, &shm_meta)) != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = mgr_task_get_layout_from_handle(tsk, &layout_tab)) != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = mpu_get_id_from_address(layout_tab, TASK_MAX_RESSOURCES_NUM, (uint32_t)shm_meta->baseaddr, &id)) != K_STATUS_OKAY)) {
        goto err;
    }
    /* detect if tsk is owner or user. must not fail */
    status = mgr_mm_shm_get_task_type(shm, tsk, &user);
    /*@ assert (status == K_STATUS_OKAY); */
    if (unlikely(user == SHM_TSK_NONE)) {
        /* this should not happen ! */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    status = mgr_task_remove_resource(tsk, mgr_mm_region_to_layout_id(id));
    /*@ assert (status == K_STATUS_OKAY); */

    status = mgr_mm_shm_set_mapflag(shm, user, SECURE_FALSE);
    /*@ assert (status == K_STATUS_OKAY); */
err:
    return status;
}


/*
 * @brief initialize MPU and configure kernel layout
 *
 * layout is the following:
 *
 * In kernel mode (syscalls):
 *                                                     S     U
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---]
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---]
 * [MPU REG 2] [ kernel current device, if needed  ] |RW-] [---] SO
 * [MPU REG 3] [ task Data SVC-exchange region     ] [RW-] [RW-]
 * [MPU REG 4] [                                   ] [---] [---]
 * [MPU REG 5] [                                   ] [---] [---]
 * [MPU REG 6] [                                   ] [---] [---]
 * [MPU REG 7] [                                   ] [---] [---]
 *
 * In User mode:
 *
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---] // syscall gate
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---] // syscall gate
 * [MPU REG 2] [ task TXT section                  ] [R-X] [R-X]
 * [MPU REG 3] [ task Data section                 ] [RW-] [RW-]
 * [MPU REG 4] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 5] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 6] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 7] [ task ressources bank 1, if needed ] [---] [---]
 *
 */
kstatus_t mgr_mm_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    mm_configured = SECURE_FALSE;

#ifdef CONFIG_HAS_MPU
    mpu_disable();
    status = mgr_mm_map_kernel_txt();
    /*@ assert (status == K_STATUS_OKAY); */
    status = mgr_mm_map_kernel_data();
    /*@ assert (status == K_STATUS_OKAY); */
    mpu_enable();
    mm_configured = SECURE_TRUE;
#endif
    /*@ assert (status == K_STATUS_OKAY); */
    return status;
}

/**
 * @brief forge an empty task memory layout
 *
 * all task memory regions are set as invalid
 */
kstatus_t mgr_mm_forge_empty_table(layout_resource_t *ressource_tab)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(ressource_tab == NULL)) {
        goto err;
    }
    for (uint8_t i = 0; i < TASK_MAX_RESSOURCES_NUM;++i) {
        mpu_forge_unmapped_ressource(i, ressource_tab);
        ressource_tab++;
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief forge a ressource opaque entry for the entry layout table
 *
 * all task memory regions are set as invalid
 */
kstatus_t mgr_mm_forge_ressource(mm_region_t reg_type, taskh_t t, layout_resource_t *ressource)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    const task_meta_t *meta;
    struct mpu_region_desc mpu_cfg;
    if (unlikely((status = mgr_task_get_metadata(t, &meta)) == K_ERROR_INVPARAM)) {
        /* invalid task handle */
        pr_err("failed to get metadata for task %08x", t);
        goto err;
    }
    switch (reg_type) {
        case MM_REGION_TASK_TXT:
            mpu_cfg.id = MM_REGION_TASK_TXT;
            mpu_cfg.addr = (uint32_t)meta->s_text;
            mpu_cfg.size = mpu_convert_size_to_region(mgr_task_get_text_region_size(meta));
            mpu_cfg.access_perm = MPU_REGION_PERM_RO;
            mpu_cfg.access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE;
            mpu_cfg.mask = 0x0;
            mpu_cfg.noexec = false;
            mpu_cfg.shareable = false;
            mpu_forge_resource(&mpu_cfg, ressource);
            break;
        case MM_REGION_TASK_DATA:
            mpu_cfg.id = MM_REGION_TASK_DATA;
            mpu_cfg.addr = (uint32_t)meta->s_svcexchange; /* To define: where start the task RAM ? .data ? other ? */
            mpu_cfg.size = mpu_convert_size_to_region(mgr_task_get_data_region_size(meta));   /* FIXME data_size is a concat of all datas sections */
            mpu_cfg.access_perm = MPU_REGION_PERM_FULL;
            mpu_cfg.access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE;
            mpu_cfg.mask = 0x0;
            mpu_cfg.noexec = true;
            mpu_cfg.shareable = false;
            mpu_forge_resource(&mpu_cfg, ressource);
            break;
        case MM_REGION_TASK_RESSOURCE_DEVICE:
            /* TODO for other ressources */
            break;
        case MM_REGION_TASK_RESSOURCE_SHM:
            /* TODO for other ressources */
            break;
        default:
            break;
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_mm_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

kstatus_t mgr_mm_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

/**
 * @brief map a kernel device
 *
 * INFO: the kernel can map a single SoC device at a time. Be cautious.
 * This function do not check that a previous device is mapped, for performance
 * reasons. This is a kernel local specific behavior.
 *
 * This API is BSP specific, not using handles, as BSP do not know handles but yet
 * needs to map themselves. This API then use address/len informations of devices
 *
 * @param[in] address: device base address
 * @param[in] size: device size
 */
kstatus_t mgr_mm_map_kdev(uint32_t address, size_t len)
{
    kstatus_t status = K_STATUS_OKAY;
    if (mgr_mm_configured() == SECURE_TRUE) {
        struct mpu_region_desc kdev_config = {
            .id = MM_REGION_KERNEL_DEVICE,
            .addr = address,
            .size = mpu_convert_size_to_region(len),
            .access_perm = MPU_REGION_PERM_PRIV,
            .access_attrs = MPU_REGION_ATTRS_DEVICE,
            .mask = 0x0,
            .noexec = true,
            .shareable = false,
        };
        status = mpu_load_descriptors(&kdev_config, 1);
    }
    return status;
}

/**
 * @brief unmap a kernel device
 *
 * INFO: this function clear and disable the kernel device region. If nothing is
 * mapped, this has no impact (other than time cost).
 *
 * This API is BSP specific, not using handles, as BSP do not know handles but yet
 * needs to map themselves. This API then use address/len informations of devices
 */
kstatus_t mgr_mm_unmap_kdev(void)
{
    kstatus_t status = K_STATUS_OKAY;
    if (likely(mgr_mm_configured() == SECURE_TRUE)) {
        mpu_clear_region(MM_REGION_KERNEL_DEVICE);
    }
    return status;
}
