// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef PMP_H
#define PMP_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#include "sentry/ktypes.h"
#include "sentry/zlib/math.h"

#include <sentry/arch/asm-generic/panic.h>

/**
 * @brief Opaque handle to a PMP entry
 *
 * TODO: implement it
 */
typedef uint32_t layout_resource_t;

#define TASK_FIRST_REGION_NUMBER 2
#define TASK_MAX_RESSOURCES_NUM (6)

/** MPU Access Permission privileged access only */
#define MPU_REGION_PERM_PRIV 0
/** MPU Access Permission full access */
#define MPU_REGION_PERM_FULL 1
/** MPU Access Permission privileged access read-only */
#define MPU_REGION_PERM_PRIV_RO 2
/** MPU Access Permission privileged/unprivileged read-only access */
#define MPU_REGION_PERM_RO 3

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

struct mpu_region_desc
{
  uint32_t addr;         /**< memory region start addr (must be align on 32 bytes boundary) */
  uint32_t size;         /**< memory region size => arch dependant */
  uint8_t id;            /**< memory region ID */
  uint8_t access_perm;   /**< Read Write access permission for supervisor and/or user mode*/
  uint8_t mask;          /**< sub region enable mask */
  uint32_t access_attrs; /**< Cached/Buffered/Shared access attributes */
  bool noexec;           /**< No-exec bit */
  bool shareable;        /**< Shared bit */
};

// TODO: make minimum region size configurable
#define PMP_MIN_REG_SIZE 4UL

// TODO: get number of PMP region from Kconfig
#define _PMP_NB_REGIONS 8

/**
 * @brief Return number of supported regions in current PMP
 */
/*@
  assigns \nothing;
*/
static inline uint32_t mpu_get_nr_regions(void)
{
  return _PMP_NB_REGIONS;
}

/**
 * @brief Reset all pmpcfg registers
 *
 * TODO: handle locked configurations
 *
 * Some memory regions could have been locked during the boot phase
 */
static inline void _mpu_initialize(void)
{
  // TODO: rework the switch to loop across all config and:
  //  - check if it is locked
  //  - if not reset it
  switch (mpu_get_nr_regions())
  {
  /* Fall through configuration of all available pmpcfg registers */
  case 64:
    __asm__ volatile("csrw pmpcfg15, zero");
    __asm__ volatile("csrw pmpcfg14, zero");
    __asm__ volatile("csrw pmpcfg13, zero");
    __asm__ volatile("csrw pmpcfg12, zero");
    __asm__ volatile("csrw pmpcfg11, zero");
    __asm__ volatile("csrw pmpcfg10, zero");
    __asm__ volatile("csrw pmpcfg9, zero");
    __asm__ volatile("csrw pmpcfg8, zero");
  case 32:
    __asm__ volatile("csrw pmpcfg7, zero");
    __asm__ volatile("csrw pmpcfg5, zero");
    __asm__ volatile("csrw pmpcfg5, zero");
    __asm__ volatile("csrw pmpcfg4, zero");
  case 16:
    __asm__ volatile("csrw pmpcfg3, zero");
    __asm__ volatile("csrw pmpcfg2, zero");
  case 8:
    __asm__ volatile("csrw pmpcfg1, zero");
  case 4:
    __asm__ volatile("csrw pmpcfg0, zero");
    break;

  default:
    /* Invalid number of PMP regions */
    panic(PANIC_HARDWARE_INVALID_STATE);
    break;
  }
}

/**
 * @brief Initialize the PMP
 */
static inline void mpu_enable(void)
{
  // if (unlikely(mpu_get_nr_regions() != CONFIG_NUM_MPU_REGIONS)) {
  //   panic(PANIC_HARDWARE_INVALID_STATE);
  // }
  // _mpu_initialize();
}

/**
 * @brief Disable the PMP
 */
static inline void mpu_disable(void)
{
}

static inline uint32_t mpu_convert_size_to_region(uint32_t size)
{
  // if (unlikely(size < PMP_MIN_REG_SIZE)) {
  //   size = PMP_MIN_REG_SIZE; /* Rounding to minimum PMP size */
  // }

  // // NA4 and NAPOT size must be power of two
  // return ROUND_UP_POW2(size, PMP_MIN_REG_SIZE);
  return 0;
}

static inline kstatus_t mpu_forge_resource(const struct mpu_region_desc *desc,
                                           layout_resource_t *resource)
{
  kstatus_t status = K_ERROR_INVPARAM;

  // // Test that address and size are correctly aligned
  // if (unlikely((0 == (desc->addr & PMP_MIN_REG_SIZE - 1)) ||
  //               (0 == (desc->size & PMP_MIN_REG_SIZE -1))) ) {
  //   return status;
  // }

  // // Find available pmp region
  // for (uint8_t i = 0; i < _PMP_NB_REGIONS; ++i) {

  // }

  // // Test if it fits in the memory map

  // // Create the region

  return status;
}

static inline void __mpu_fastload(
    uint32_t first_region_number,
    const layout_resource_t *resource,
    uint8_t num_resources)
{
  // TODO
}

static inline kstatus_t mpu_load_descriptors(
    const struct mpu_region_desc *region_descs,
    size_t count)
{
  kstatus_t status = K_ERROR_INVPARAM;

  // TODO

  return status;
}

static inline kstatus_t mpu_forge_unmapped_ressource(uint8_t id, layout_resource_t *resource)
{
  kstatus_t status = K_ERROR_INVPARAM;

  // TODO

  return status;
}

static inline void mpu_fastload(
    uint32_t first_region_number,
    const layout_resource_t *resource,
    uint8_t num_resources)
{
  mpu_disable();
  __mpu_fastload(first_region_number, resource, num_resources);
  mpu_enable();
}

static inline kstatus_t mpu_get_id_from_address(
    const layout_resource_t *resource,
    uint8_t num_resources,
    size_t addr,
    uint8_t *id)
{
  kstatus_t status = K_ERROR_NOENT;

  // TODO

  return status;
}

#ifndef CONFIG_BUILD_TARGET_AUTOTEST
static inline
#else
static
#endif
    kstatus_t
    mpu_get_free_id(const layout_resource_t *resource, uint8_t num_resources, uint8_t *id)
{
  kstatus_t status = K_ERROR_NOENT;

  // TODO

  return status;
}

static inline void mpu_clear_region(uint32_t rnr)
{
  // TODO
}

#endif /* PMP_H */