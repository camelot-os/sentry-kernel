/*
 * SPDX-FileCopyrightText: 2023 Ledger SAS
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * MPU implementation header for PMSAv7 ARM cortex-M MPU.
 */

#ifndef __ARCH_MPU_H
#error "this is an arch specific header, **do not** include directly, use <arch/mpu.h> instead"
#endif

#ifndef __ARCH_ARM_PMSA_V7_H
#define __ARCH_ARM_PMSA_V7_H

#include <inttypes.h>
#include <stddef.h>

#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/ktypes.h>
#include <sentry/zlib/math.h>

/** MPU Access Permission no access */
#define MPU_REGION_PERM_NONE ARM_MPU_AP_NONE
/** MPU Access Permission privileged access only */
#define MPU_REGION_PERM_PRIV ARM_MPU_AP_PRIV
/** MPU Access Permission privileged read-write, unprivileged access read-only */
#define MPU_REGION_PERM_UNPRIV_RO ARM_MPU_AP_URO
/** MPU Access Permission full access */
#define MPU_REGION_PERM_FULL ARM_MPU_AP_FULL
/** MPU Access Permission privileged access read-only */
#define MPU_REGION_PERM_PRIV_RO ARM_MPU_AP_PRO
/** MPU Access Permission privileged/unprivileged read-only access */
#define MPU_REGION_PERM_RO ARM_MPU_AP_RO

/** MPU Access attribute for strongly ordered memory */
#define MPU_REGION_ATTRS_STRONGLY_ORDER ARM_MPU_ACCESS_ORDERED
/** MPU Access attribute for device memory */
#define MPU_REGION_ATTRS_DEVICE ARM_MPU_ACCESS_DEVICE(0UL)

/** MPU Access attribute for non cached normal memory */
#define MPU_REGION_ATTRS_NORMAL_NOCACHE \
    ARM_MPU_ACCESS_NORMAL(ARM_MPU_CACHEP_NOCACHE, ARM_MPU_CACHEP_NOCACHE, 0UL)

/** MPU Access attribute for cached normal memory w/ write back and read allocate cache policy */
#define MPU_REGION_ATTRS_NORMAL_CACHE \
    ARM_MPU_ACCESS_NORMAL(ARM_MPU_CACHEP_WB_NWA, ARM_MPU_CACHEP_WB_NWA, 0UL)

/** MPU Access attribute for cached and shared normal memory w/ write back and read allocate cache policy */
#define MPU_REGION_ATTRS_NORMAL_CACHE_SHARED \
    ARM_MPU_ACCESS_NORMAL(ARM_MPU_CACHEP_WB_NWA, ARM_MPU_CACHEP_WB_NWA, 1UL)

/** MPU Region Size 32 Bytes */
#define MPU_REGION_SIZE_32B ARM_MPU_REGION_SIZE_32B
/** MPU Region Size 64 Bytes */
#define MPU_REGION_SIZE_64B ARM_MPU_REGION_SIZE_64B
/** MPU Region Size 128 Bytes */
#define MPU_REGION_SIZE_128B ARM_MPU_REGION_SIZE_128B
/** MPU Region Size 256 Bytes */
#define MPU_REGION_SIZE_256B ARM_MPU_REGION_SIZE_256B
/** MPU Region Size 512 Bytes */
#define MPU_REGION_SIZE_512B ARM_MPU_REGION_SIZE_512B
/** MPU Region Size 1 KByte */
#define MPU_REGION_SIZE_1KB ARM_MPU_REGION_SIZE_1KB
/** MPU Region Size 2 KBytes */
#define MPU_REGION_SIZE_2KB ARM_MPU_REGION_SIZE_2KB
/** MPU Region Size 4 KBytes */
#define MPU_REGION_SIZE_4KB ARM_MPU_REGION_SIZE_4KB
/** MPU Region Size 8 KBytes */
#define MPU_REGION_SIZE_8KB ARM_MPU_REGION_SIZE_8KB
/** MPU Region Size 16 KBytes */
#define MPU_REGION_SIZE_16KB ARM_MPU_REGION_SIZE_16KB
/** MPU Region Size 32 KBytes */
#define MPU_REGION_SIZE_32KB ARM_MPU_REGION_SIZE_32KB
/** MPU Region Size 64 KBytes */
#define MPU_REGION_SIZE_64KB ARM_MPU_REGION_SIZE_64KB
/** MPU Region Size 128 KBytes */
#define MPU_REGION_SIZE_128KB ARM_MPU_REGION_SIZE_128KB
/** MPU Region Size 256 KBytes */
#define MPU_REGION_SIZE_256KB ARM_MPU_REGION_SIZE_256KB
/** MPU Region Size 512 KBytes */
#define MPU_REGION_SIZE_512KB ARM_MPU_REGION_SIZE_512KB
/** MPU Region Size 1 MByte */
#define MPU_REGION_SIZE_1MB ARM_MPU_REGION_SIZE_1MB
/** MPU Region Size 2 MBytes */
#define MPU_REGION_SIZE_2MB ARM_MPU_REGION_SIZE_2MB
/** MPU Region Size 4 MBytes */
#define MPU_REGION_SIZE_4MB ARM_MPU_REGION_SIZE_4MB
/** MPU Region Size 8 MBytes */
#define MPU_REGION_SIZE_8MB ARM_MPU_REGION_SIZE_8MB
/** MPU Region Size 16 MBytes */
#define MPU_REGION_SIZE_16MB ARM_MPU_REGION_SIZE_16MB
/** MPU Region Size 32 MBytes */
#define MPU_REGION_SIZE_32MB ARM_MPU_REGION_SIZE_32MB
/** MPU Region Size 64 MBytes */
#define MPU_REGION_SIZE_64MB ARM_MPU_REGION_SIZE_64MB
/** MPU Region Size 128 MBytes */
#define MPU_REGION_SIZE_128MB ARM_MPU_REGION_SIZE_128MB
/** MPU Region Size 256 MBytes */
#define MPU_REGION_SIZE_256MB ARM_MPU_REGION_SIZE_256MB
/** MPU Region Size 512 MBytes */
#define MPU_REGION_SIZE_512MB ARM_MPU_REGION_SIZE_512MB
/** MPU Region Size 1 GByte */
#define MPU_REGION_SIZE_1GB ARM_MPU_REGION_SIZE_1GB
/** MPU Region Size 2 GBytes */
#define MPU_REGION_SIZE_2GB ARM_MPU_REGION_SIZE_2GB
/** MPU Region Size 4 GBytes */
#define MPU_REGION_SIZE_4GB ARM_MPU_REGION_SIZE_4GB

/*@
  assigns \nothing;
 */
__STATIC_FORCEINLINE void __mpu_initialize(void)
{
    /* Nothing to do for PMSAv7 */
}

/*@
   requires \valid(resource);
   assigns *resource;
 */
__STATIC_FORCEINLINE kstatus_t mpu_forge_unmapped_ressource(uint8_t id, layout_resource_t* resource)
{
    kstatus_t status = K_ERROR_INVPARAM;

    resource->RBAR = ARM_MPU_RBAR(id + TASK_FIRST_REGION_NUMBER, 0x0UL);
    resource->RASR = 0x0UL;
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
    uint32_t rbar;
    uint32_t rasr;


    /* W^X conformity */
    /*@
      assert desc->noexec == 0 ==>
        (desc->access_perm == MPU_REGION_PERM_RO || desc->access_perm == MPU_REGION_PERM_PRIV_RO);
     */
    /*@
      assert (desc->access_perm != MPU_REGION_PERM_RO && desc->access_perm != MPU_REGION_PERM_PRIV_RO) ==>
        desc->noexec == 1;
    */
    resource->RBAR = ARM_MPU_RBAR(desc->id, desc->addr);
    resource->RASR = ARM_MPU_RASR_EX(desc->noexec ? 1UL : 0UL,
                           desc->access_perm,
                           desc->access_attrs,
                           desc->mask,
                           desc->size);
    status = K_STATUS_OKAY;
    return status;
}

/**
 * @brief PMSAv7 MPU region fastload
 *
 * @param first_region_number MPU region number for the first region to be loaded
 * @param resource resource layout table
 * @param num_resources number of resources to (fast) load
 *
 * @note for PMSAv7, resource ID is encoded in RBAR register,
 * thus, first_region_number is unused.
 */
/*@
  requires \valid_read(resource + (0 .. num_resources-1));
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void __mpu_fastload(
    uint32_t first_region_number __attribute__((unused)),
    const layout_resource_t *resource,
    uint8_t num_resources
){
    ARM_MPU_Load(resource, num_resources);
}

/*@
   requires \valid_read(resource);
   assigns \nothing;
 */
__STATIC_FORCEINLINE secure_bool_t __mpu_is_resource_free(const layout_resource_t* resource)
{
    secure_bool_t is_free = SECURE_FALSE;

    if (resource->RASR == 0x0UL) {
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
    return resource->RBAR & MPU_RBAR_ADDR_Msk;
}

/**
 * @brief PMSAv7 MPU region size alignment
 * @param size memory size to map
 * @return size aligned the next power of 2 boundary if unaligned
 */
/*@
   assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t __mpu_region_align_size(uint32_t size)
{
    /* TODO overflow check here */
    if (unlikely(!IS_POW2(size))) {
        size = ALIGN_TO_POW2(size);
    }

    return size;
}

/**
 * @brief convert size in PMSAv7 format
 *
 * @param size region size (must be aligned to power of 2)
 *
 * Size configuration in RASR is 2^(N+1)
 * This function computes N from an already aligned size.
 *
 * @return the value to write into the RASR
 */
/*@
   assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t __mpu_size_to_region(uint32_t size)
{
    uint8_t shift = __builtin_ffsl(size) - 1;
    /*
     * MPU region size is correlated to the shift value, starting with 32B=0x4.
     * 32 is encoded with 0b100000 (shift == 5). We only have to return shift - 1
     * to get the correct result
     */
    return shift - 1;
}

/*@
  // TODO: get back local SoC max RNR to control region_id value
  requires \valid_read(resource);
  assigns (*(MPU_Type*)MPU_BASE);
 */
__STATIC_FORCEINLINE void __mpu_set_region(
    uint32_t region_id __attribute__((unused)),
    const layout_resource_t *resource
)
{
    ARM_MPU_SetRegion(resource->RBAR, resource->RASR);
}

#endif /* __ARCH_ARM_PMSA_V7_H */
