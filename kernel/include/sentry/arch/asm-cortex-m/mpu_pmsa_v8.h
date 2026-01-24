// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * MPU implementation header for PMSAv8 ARM cortex-M MPU.
 */

#ifndef __ARCH_MPU_H
#error "this is an arch specific header, **do not** include directly, use <arch/mpu.h> instead"
#endif

#ifndef __ARCH_ARM_PMSA_V8_H
#define __ARCH_ARM_PMSA_V8_H

#include <inttypes.h>
#include <stddef.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/ktypes.h>
#include <sentry/zlib/math.h>

#define _PMSAv8_MEM_ALIGNMENT 32UL

#define _MPU_PERM_RW 0
#define _MPU_PERM_RO 1
#define _MPU_PERM_P  0
#define _MPU_PERM_NP 1

#define _MPU_ATTR_CACHE_WB_RA ARM_MPU_ATTR_MEMORY_(0, 1, 1, 0)

/** MPU Access Permission privileged access only */
#define MPU_REGION_PERM_PRIV ARM_MPU_AP_(_MPU_PERM_RW, _MPU_PERM_P)
/** MPU Access Permission full access */
#define MPU_REGION_PERM_FULL ARM_MPU_AP_(_MPU_PERM_RW, _MPU_PERM_NP)
/** MPU Access Permission privileged access read-only */
#define MPU_REGION_PERM_PRIV_RO ARM_MPU_AP_(_MPU_PERM_RO, _MPU_PERM_P)
/** MPU Access Permission privileged/unprivileged read-only access */
#define MPU_REGION_PERM_RO ARM_MPU_AP_(_MPU_PERM_RO, _MPU_PERM_NP)

#define MPU_REGION_ALIGN 32U
#define MPU_REGION_ALIGN_MASK (MPU_REGION_ALIGN - 1)

/*
 * XXX:
 *  For armv8, memory attribute are shared between region and programmed to
 *  MPU Memory Attribute Indirection Registers 0 and 1.
 *  Each region may point to the attr index the wanna use.
 *
 *  This is hardcoded.
 *   - 0: device memory strongly ordered
 *   - 1: normal memory nocache
 *   - 2: normal memory cache, writeback, read allocate
 */

/** MPU Access attribute for device memory */
#define MPU_REGION_ATTRS_DEVICE 0
/** MPU Access attribute for non cached normal memory */
#define MPU_REGION_ATTRS_NORMAL_NOCACHE 1
/** MPU Access attribute for cached normal memory w/ write back and read allocate cache policy */
#define MPU_REGION_ATTRS_NORMAL_CACHE 2


/** MPU Region Size 32 Bytes */
#define MPU_REGION_SIZE_32B 32UL
/** MPU Region Size 64 Bytes */
#define MPU_REGION_SIZE_64B 64UL
/** MPU Region Size 128 Bytes */
#define MPU_REGION_SIZE_128B 128UL
/** MPU Region Size 256 Bytes */
#define MPU_REGION_SIZE_256B 256UL
/** MPU Region Size 512 Bytes */
#define MPU_REGION_SIZE_512B 512UL
/** MPU Region Size 1 KByte */
#define MPU_REGION_SIZE_1KB (1UL * KBYTE)
/** MPU Region Size 2 KBytes */
#define MPU_REGION_SIZE_2KB (2UL * KBYTE)
/** MPU Region Size 4 KBytes */
#define MPU_REGION_SIZE_4KB (4UL * KBYTE)
/** MPU Region Size 8 KBytes */
#define MPU_REGION_SIZE_8KB (8UL * KBYTE)
/** MPU Region Size 16 KBytes */
#define MPU_REGION_SIZE_16KB (16UL * KBYTE)
/** MPU Region Size 32 KBytes */
#define MPU_REGION_SIZE_32KB (32UL * KBYTE)
/** MPU Region Size 64 KBytes */
#define MPU_REGION_SIZE_64KB (64UL * KBYTE)
/** MPU Region Size 128 KBytes */
#define MPU_REGION_SIZE_128KB (128UL * KBYTE)
/** MPU Region Size 256 KBytes */
#define MPU_REGION_SIZE_256KB (256UL * KBYTE)
/** MPU Region Size 512 KBytes */
#define MPU_REGION_SIZE_512KB (512UL * KBYTE)
/** MPU Region Size 1 MByte */
#define MPU_REGION_SIZE_1MB (1UL * MBYTE)
/** MPU Region Size 2 MBytes */
#define MPU_REGION_SIZE_2MB (2UL * MBYTE)
/** MPU Region Size 4 MBytes */
#define MPU_REGION_SIZE_4MB (4UL * MBYTE)
/** MPU Region Size 8 MBytes */
#define MPU_REGION_SIZE_8MB (8UL * MBYTE)
/** MPU Region Size 16 MBytes */
#define MPU_REGION_SIZE_16MB (16UL * MBYTE)
/** MPU Region Size 32 MBytes */
#define MPU_REGION_SIZE_32MB (32UL * MBYTE)
/** MPU Region Size 64 MBytes */
#define MPU_REGION_SIZE_64MB (64UL * MBYTE)
/** MPU Region Size 128 MBytes */
#define MPU_REGION_SIZE_128MB (128UL * MBYTE)
/** MPU Region Size 256 MBytes */
#define MPU_REGION_SIZE_256MB (256UL * MBYTE)
/** MPU Region Size 512 MBytes */
#define MPU_REGION_SIZE_512MB (512UL * MBYTE)
/** MPU Region Size 1 GByte */
#define MPU_REGION_SIZE_1GB (1UL * GBYTE)
/** MPU Region Size 2 GBytes */
#define MPU_REGION_SIZE_2GB (2UL * GBYTE)

/** @brief Region Base Address Register value
* @param BASE The base address bits [31:5] of a memory region. The value is zero extended. Effective address gets 32 byte aligned.
* @param SH Defines the Shareability domain for this memory region.
* @param AP Access Premission: As defined by @ref ARM_MPU_AP_
* @param XN eXecute Never: Set to 1 for a non-executable memory region.
*/
#define ARM_MPU_RBAR_AP(BASE, SH, AP, XN) \
  (((BASE) & MPU_RBAR_BASE_Msk) | \
  (((SH) << MPU_RBAR_SH_Pos) & MPU_RBAR_SH_Msk) | \
  (((AP) << MPU_RBAR_AP_Pos) & MPU_RBAR_AP_Msk) | \
  (((XN) << MPU_RBAR_XN_Pos) & MPU_RBAR_XN_Msk))

#define MPU_FASTLOAD_ALIGNED 1


/*@

  predicate aligned_32(ℤ addr) =
    (addr & MPU_REGION_ALIGN_MASK) == 0;

  predicate valid_mpu_region(ℤ base, ℤ limit) =
       aligned_32(base)
    && aligned_32(limit)
    && limit >= base
    && ((limit - base + 1) % MPU_REGION_ALIGN == 0);

  predicate valid_mpu_regions{L}(ARM_MPU_Region_t *regions, integer n) =
        \forall integer i;
            0 <= i < n ==>
            valid_mpu_region(regions[i].RBAR & MPU_RBAR_BASE_Msk,
                             regions[i].RLAR & MPU_RLAR_LIMIT_Msk);

  predicate non_empty_region(ℤ base, ℤ limit) =
    (limit - base + 1) >= MPU_REGION_ALIGN;

  predicate disjoint(ARM_MPU_Region_t r1, ARM_MPU_Region_t r2) =
      r1.RBAR <= r2.RLAR || r2.RBAR <= r1.RLAR;

  predicate regions_disjoint{L}(ARM_MPU_Region_t *regions, integer n) =
      \forall integer i, j;
        0 <= i < n && 0 <= j < n && i != j ==>
          disjoint(regions[i], regions[j]);
*/


/*@
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void __mpu_initialize(void)
{
    size_t mpu_attr_size;
    /*
     * Fixme: we may define flags closer to the real configuration
     * e.g. write-back/write-through, read_allocate, write_allocate.
     */
    const uint8_t _mpu_attrs[] = {
        /** MPU Access attribute for device memory */
        ARM_MPU_ATTR(ARM_MPU_ATTR_DEVICE, ARM_MPU_ATTR_DEVICE_nGnRnE),
        /** MPU Access attribute for non cached normal memory */
        ARM_MPU_ATTR(ARM_MPU_ATTR_NON_CACHEABLE, ARM_MPU_ATTR_NON_CACHEABLE),
        /** MPU Access attribute for cached normal memory w/ write back and read allocate cache policy */
        ARM_MPU_ATTR(ARM_MPU_ATTR_NON_CACHEABLE, ARM_MPU_ATTR_NON_CACHEABLE),
    };

    static_assert(ARRAY_SIZE(_mpu_attrs) <= 8, "PMSAv8 MPU attribute array size too big");
    mpu_attr_size = ARRAY_SIZE(_mpu_attrs);
    /*@
        loop invariant 0 <= idx <= mpu_attr_size;
        loop assigns (*(MPU_Type*)MPU_BASE);
        loop variant mpu_attr_size - idx;
    */
    for (uint8_t idx = 0; idx < mpu_attr_size; idx++) {
        ARM_MPU_SetMemAttr(idx, _mpu_attrs[idx]);
    }
}

/*@
   requires \valid(resource);
   assigns *resource;
 */
__STATIC_FORCEINLINE kstatus_t mpu_forge_unmapped_ressource(uint8_t id, layout_resource_t *resource)
{
    kstatus_t status = K_ERROR_INVPARAM;
    resource->RBAR = 0x0UL;
    resource->RLAR = 0x0UL;
    status = K_STATUS_OKAY;
    return status;
}

/*@
  requires \valid_read(desc);
  requires \valid(resource);
  assigns *resource;
  ensures (\result == K_STATUS_OKAY);
 */
__STATIC_FORCEINLINE kstatus_t mpu_forge_resource(const struct mpu_region_desc *desc,
                                                   layout_resource_t *resource)
{
    kstatus_t status = K_ERROR_INVPARAM;

    /* W^X conformity */
    /*@
      assert desc->noexec == 0 ==>
        (desc->access_perm == MPU_REGION_PERM_RO || desc->access_perm == MPU_REGION_PERM_PRIV_RO);
     */
    /*@
      assert (desc->access_perm != MPU_REGION_PERM_RO && desc->access_perm != MPU_REGION_PERM_PRIV_RO) ==>
        desc->noexec == 1;
    */
    resource->RBAR = ARM_MPU_RBAR_AP(
        desc->addr,
        desc->shareable ? ARM_MPU_SH_INNER : ARM_MPU_SH_NON,
        desc->access_perm,
        desc->noexec ? 1UL : 0UL
    );

    resource->RLAR = ARM_MPU_RLAR(desc->addr + desc->size - 1, desc->access_attrs);

    status = K_STATUS_OKAY;
    /*@ assert (status == K_STATUS_OKAY); */
    return status;
}


/**
 * Compare two ARMv8-M MPU regions defined by RBAR/RLAR
 *
 * @return true if regions overlap, false otherwise
 */
static inline secure_bool_t mpu_regions_overlap(layout_resource_t reg1, layout_resource_t reg2)
{
    secure_bool_t overlap = SECURE_TRUE;
    uint32_t base_a  = reg1.RBAR & MPU_RBAR_BASE_Msk;
    uint32_t limit_a = reg1.RLAR & MPU_RBAR_BASE_Msk;

    uint32_t base_b  = reg2.RBAR & MPU_RBAR_BASE_Msk;
    uint32_t limit_b = reg2.RLAR & MPU_RBAR_BASE_Msk;

    /* Invalid or disabled regions never overlap */
    if (limit_a < base_a || limit_b < base_b) {
        overlap = SECURE_FALSE;
    }

    /* Convert inclusive limit to exclusive end */
    uint64_t end_a = (uint64_t)limit_a + MPU_REGION_ALIGN;
    uint64_t end_b = (uint64_t)limit_b + MPU_REGION_ALIGN;

    if ((base_a >= end_b) || (base_b >= end_a)) {
        overlap = SECURE_FALSE;
    }
    return overlap;
}

/**
 * @brief PMSAv8 MPU region fastload
 *
 * @param first_region_number MPU region number for the first region to be loaded
 * @param resource resource layout table
 * @param num_resources number of resources to (fast) load
 *
 * @note for PMSAv8, resource ID must be written before setting MPU region RBAR/RLAR.
 * In case of fast loading, write RNR reg to the first region number, fast load up
 * to 4 region, refresh RNR, write next 4 regions and so one. This is handle by CMSIS
 * intrinsics.
 */
/*@
  requires \valid_read(resource + (0 .. num_resources-1));
  requires ((first_region_number + num_resources) <= CONFIG_NUM_MPU_REGIONS);
  requires valid_mpu_regions(resource, num_resources);
  requires regions_disjoint(resource, num_resources);
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void __mpu_fastload(
    uint32_t first_region_number,
    const layout_resource_t *resource,
    uint8_t num_resources
)
{

    ARM_MPU_Load(first_region_number, resource, num_resources);
}

/*@
   requires \valid_read(resource);
   assigns \nothing;
 */
__STATIC_FORCEINLINE secure_bool_t __mpu_is_resource_free(const layout_resource_t *resource)
{
    secure_bool_t is_free = SECURE_FALSE;

    if ((resource->RLAR == 0x0UL) && (resource->RBAR == 0x0UL)) {
        is_free = SECURE_TRUE;
    }

    return is_free;
}

/*@
   requires \valid_read(resource);
   assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t __mpu_get_resource_base_address(const layout_resource_t *resource)
{
    return resource->RBAR & MPU_RBAR_BASE_Msk;
}

/**
 * @brief PMSAv8 MPU region size alignment
 * @param size memory size to map
 * @return size aligned the next 32 bytes boundary if unaligned
 */
/*@
   assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t __mpu_region_align_size(uint32_t size)
{
    return ROUND_UP_POW2(size, _PMSAv8_MEM_ALIGNMENT);
}

/*@
   assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t __mpu_size_to_region(uint32_t size)
{
    /* Nothing to do for PMSAv8 */
    return size;
}

/*@
  requires region_id < CONFIG_NUM_MPU_REGIONS;
  requires \valid_read(resource);
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void __mpu_set_region(
    uint32_t region_id,
    const layout_resource_t *resource
)
{
    ARM_MPU_SetRegion(region_id, resource->RBAR, resource->RLAR);
}

#endif /* __ARCH_ARM_PMSA_V8_H */
