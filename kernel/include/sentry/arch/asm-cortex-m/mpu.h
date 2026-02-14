// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __ARCH_MPU_H
#define __ARCH_MPU_H

/**
 * \file MPU manipulation API for upper layer (memory unit)
 */
#include <stdint.h>
#include <stdbool.h>

#include <sentry/arch/asm-generic/panic.h>

struct mpu_region_desc {
    uint32_t addr;          /**< memory region start addr (must be align on 32 bytes boundary) */
    uint32_t size;          /**< memory region size => arch dependant */
    uint8_t  id;            /**< memory region ID */
    uint8_t  access_perm;   /**< Read Write access permission for supervisor and/or user mode*/
    uint8_t  mask;          /**< sub region enable mask */
    uint32_t access_attrs;  /**< Cached/Buffered/Shared access attributes */
    bool     noexec;        /**< No-exec bit */
    bool     shareable;     /**< Shared bit */
};

/*
 * a mpu ressource is a layout_resource_t opaque.
 * On PMSAv7 this is the concatenation of RBAR & RASR registers values.
 * On PMSAv8 this is the concatenation of RBAR & RLAR registers values.
 * A task hold a table of this opaque, allowing store/fastload multiple regions
 * and efficiently keep trace of currently mapped regions.
 */
typedef ARM_MPU_Region_t layout_resource_t;

/*
 * Region 0/1 are reserved for kernel usage
 * Region starting from 2 to 'CONFIG_NUM_MPU_REGIONS' are reserved for user task
 */
#define TASK_FIRST_REGION_NUMBER 2
#define TASK_MAX_RESSOURCES_NUM (CONFIG_NUM_MPU_REGIONS - TASK_FIRST_REGION_NUMBER)

#if defined(CONFIG_ARCH_ARM_CORTEX_M) && \
    defined(CONFIG_HAS_MPU) && \
    defined(CONFIG_HAS_MPU_PMSA_V7)

#include <sentry/arch/asm-cortex-m/mpu_pmsa_v7.h>

#elif defined(CONFIG_ARCH_ARM_CORTEX_M) && \
      defined(CONFIG_HAS_MPU) && \
      defined(CONFIG_HAS_MPU_PMSA_V8)

/** FIXME: header to write, this will fail at compile time */
#include <sentry/arch/asm-cortex-m/mpu_pmsa_v8.h>
#else
# error "Unknown MPU type!"
#endif

/**
 * Number of supported region in current MPU
 */
/*@ assigns \nothing; */
__STATIC_FORCEINLINE uint32_t mpu_get_nr_regions(void)
{
    return (MPU->TYPE & MPU_TYPE_DREGION_Msk) >> MPU_TYPE_DREGION_Pos;
}

/**
 * Enable cortex-m (PMSAv7/PMSAv8) MPU
 */
/*@
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void mpu_enable(void)
{
    if (unlikely(mpu_get_nr_regions() != CONFIG_NUM_MPU_REGIONS)) {
        panic(PANIC_HARDWARE_INVALID_STATE);
    }
    __mpu_initialize();
    ARM_MPU_Enable(MPU_CTRL_PRIVDEFENA_Msk | MPU_CTRL_HFNMIENA_Msk);
}

/**
 * Disable cortex-m (PMSAv7/PMSAv8) MPU
 */
/*@
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void mpu_disable(void)
{
    ARM_MPU_Disable();
}

/**
 * Clear (and disable) MPU region configuration
 */
/*@
  requires rnr < CONFIG_NUM_MPU_REGIONS;
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void mpu_clear_region(uint32_t rnr)
{
#ifndef __FRAMAC__
    __ISB();
    __DSB();
#endif
    ARM_MPU_ClrRegion(rnr);
#ifndef __FRAMAC__
    __ISB();
    __DSB();
#endif
}

/*@
  requires (first_region_number < CONFIG_NUM_MPU_REGIONS);
  requires \valid_read(resource);
  requires ((first_region_number + num_resources) <= CONFIG_NUM_MPU_REGIONS);
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void mpu_fastload(
    uint32_t first_region_number,
    const layout_resource_t *resource,
    uint8_t num_resources)
{
    mpu_disable();
    __mpu_fastload(first_region_number, resource, num_resources);
    mpu_enable();
}

/*
 * this is not portable as PMSAv8 does not keep track of region id in RBAR
 * layout table implies that region number are contiguous
 */

/*
 * Fixme:
 *  This should be up to the memory manager to look up in task layout tab
 *  because resource index is not related to region index.
 *  Here we should only check for free resource or not.
 *
 * XXX:
 *  Hackish for now, make assumption that this tab belongs to a task and applied
 *  an hardcoded offset.
 */
/*@
  requires \valid(id);
  requires (num_resources < CONFIG_NUM_MPU_REGIONS);
  requires \valid_read(resource + (0 .. num_resources - 1));
  assigns *id;
 */
#ifndef CONFIG_BUILD_TARGET_AUTOTEST
__STATIC_FORCEINLINE
#else
static
#endif
kstatus_t mpu_get_free_id(const layout_resource_t* resource, uint8_t num_resources, uint8_t *id)
{
    kstatus_t status = K_ERROR_NOENT;

    /*@
      loop invariant 0 <= i <= num_resources;
      loop assigns *id, status;
      loop assigns resource;
      loop variant (num_resources - i);
     */
    for (uint8_t i = 0; i < num_resources; ++i) {
        if (__mpu_is_resource_free(resource) == SECURE_TRUE) {
            *id = i;
            status = K_STATUS_OKAY;
            break;
        }
        resource++;
    }

    return status;
}

/*
 * Fixme: Same as above.
 * XXX:
 *  Hackish for now, make assumption that this tab belongs to a task and applied
 *  an hardcoded offset.
 */
/*@
  requires \valid(id);
  requires (num_resources < CONFIG_NUM_MPU_REGIONS);
  requires \valid_read(resource + (0 .. num_resources - 1));
  assigns *id;
 */
__STATIC_FORCEINLINE kstatus_t mpu_get_id_from_address(
    const layout_resource_t* resource,
    uint8_t num_resources,
    size_t addr,
    uint8_t *id)
{
    kstatus_t status = K_ERROR_NOENT;

    /*@
      loop invariant 0 <= i <= num_resources;
      loop assigns *id, status;
      loop assigns resource;
      loop variant (num_resources - i);
     */
    for (uint8_t i = 0; i < num_resources; ++i) {
        if (__mpu_get_resource_base_address(resource) == addr) {
            *id = i + TASK_FIRST_REGION_NUMBER;
            status = K_STATUS_OKAY;
            break;
        }
        resource++;
    }
    return status;
}

/*@
  assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t mpu_convert_size_to_region(uint32_t size)
{
    if (unlikely(size < 32)) {
        size = 32; /* rounding to minimum MPU size supported */
    }

    size = __mpu_region_align_size(size);
    return __mpu_size_to_region(size);
}

/**
 * Load memory regions description table in MPU
 */
/*@
    // any call of this function MUST be done with valid inputs
    requires \valid_read(region_descs);
    requires \valid_read(region_descs + (0 .. count-1));
    assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE kstatus_t mpu_load_descriptors(
    const struct mpu_region_desc *region_descs,
    size_t count
)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const struct mpu_region_desc *desc = NULL;
    layout_resource_t resource;
    /*@ assert \valid_read(region_descs); */
#ifndef __FRAMAC__
    /* no meaning with Frama-C*/
    __ISB();
    __DSB();
#endif

    /*@
       loop invariant 0 <= i <= count;
       loop assigns desc;
       loop assigns resource;
       loop variant count - i;
     */
    for (size_t i = 0UL; i < count; i++) {
        desc = region_descs + i;
        if (unlikely(mpu_forge_resource(desc, &resource) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
            break;
        }
        __mpu_set_region(desc->id, &resource);
    }
#ifndef __FRAMAC__
    __ISB();
    __DSB();
#endif

    status = K_STATUS_OKAY;
    /*@ assert(status == K_STATUS_OKAY); */
    return status;
}

#endif/*__ARCH_MPU_H*/
