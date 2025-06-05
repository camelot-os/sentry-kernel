// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef PMP_H
#define PMP_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#include "sentry/ktypes.h"
#include "sentry/zlib/math.h"

#include <sentry/arch/asm-generic/panic.h>

#include <sentry/arch/asm-rv32/riscv-utils.h>

/**
 * @brief MPU region description
 *
 * @note it is based on the ARM structure for compatibility
 */
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

/**
 * @brief Opaque handle to a PMP entry
 *
 */
typedef struct layout_resource {
  uint8_t index; /* PMP entry index */
  uint8_t pmpcfg;
  uint32_t pmpaddr;
} layout_resource_t;

#define CSR_PMPCFG_BASE  0x3a0
#define CSR_PMPADDR_BASE 0x3b0

#define PMPCFG_GET(pmpcfg, index) (pmpcfg >> (index *8))
#define PMPCFG_GET_R(pmpcfg) (pmpcfg & 1)
#define PMPCFG_GET_W(pmpcfg) ((pmpcfg >> 1) & 1)
#define PMPCFG_GET_X(pmpcfg) ((pmpcfg >> 2) & 1)
#define PMPCFG_GET_A(pmpcfg) ((pmpcfg >> 3) & 3)
#define PMPCFG_GET_L(pmpcfg) ((pmpcfg >> 6) & 1)

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

// PMP granularity
static uint32_t pmp_granularity;

// Number of PMP regions
static const uint8_t NB_PMP_REGIONS = CONFIG_NUM_MPU_REGIONS;

/**
 * @brief Reset all pmpcfg registers
 *
 * TODO: handle locked configurations
 *
 * Some memory regions could have been locked during the boot phase
 */
static inline void _mpu_initialize(void)
{
  uint16_t i;

  // TODO: rework the switch to loop across all config and:
  //  - check if it is locked
  //  - if not reset it
  for (i = 0; i < NB_PMP_REGIONS/4; i++) {
    CSR_ZERO_ADDR(CSR_PMPCFG_BASE + i);
  }
}

/**
 * @brief Detect the maximum granularity supported by the core
 *
 * @note Use methode described in 'priv-spec'§3.7.12:
 *         - Write all ones to pmpaddr0, detect the position of the lsb 1
 *           set in the address
 *         - return granularity = 2^(i + 2)
 */
static inline uint32_t _mpu_get_granularity(void) {
  uint32_t i = 0;
  uint32_t addr = 0;

  CSR_WRITE_ADDR(CSR_PMPCFG_BASE, 0);
  CSR_WRITE_ADDR(CSR_PMPADDR_BASE, 0xffffffff);
  addr = CSR_READ_ADDR(CSR_PMPADDR_BASE);

  while (((addr >> i) & 1) == 0) {
    i += 1;
  }

  return (1 << (i + 2));
}

/**
 * @brief Initialize the PMP
 *
 * @note RISC-V PMP is always active, each region is activated
 */
static inline void mpu_enable(void)
{
  // Nothing to do
}

/**
 * @brief Disable the PMP
 *
 * @note mpu_disable is called first when the PMP is initialized, use this
 *    function to get the PMP configuration
 */
static inline void mpu_disable(void)
{
  // Get PMP address granularity
  pmp_granularity = _mpu_get_granularity();

  // Set all configurations to zero
  _mpu_initialize();
}

/**
 * @brief Compute the best appropriate size for a PMP region
 */
static inline uint32_t mpu_convert_size_to_region(uint32_t size)
{
  if (unlikely(size < pmp_granularity)) {
    size = pmp_granularity; /* Rounding to minimum PMP size */
  }

  // // NA4 and NAPOT size must be power of two
  return ((((size) - 1) | ((pmp_granularity) - 1)) + 1);
}

static inline kstatus_t mpu_forge_resource(const struct mpu_region_desc *desc,
                                           layout_resource_t *resource)
{
  kstatus_t status = K_ERROR_INVPARAM;
  uint8_t index = 0;
  uint32_t pmpcfg = 0;

  // Find available PMP region
  while (index < NB_PMP_REGIONS) {
    if (0 == index%4) {
      pmpcfg = CSR_READ_ADDR(CSR_PMPCFG_BASE + (index/4));
    }

    if (0 == PMPCFG_GET_A(PMPCFG_GET(pmpcfg, index%4))) {
      // Region not assigned yet
      break;
    }
  }

  if (NB_PMP_REGIONS == index) {
    // No free region has been found
    return K_ERROR_BADSTATE;
  }

  resource->index = index;
  resource->pmpaddr = desc->addr;

  status = K_STATUS_OKAY;
  /*@ assert (status == K_STATUS_OKAY); */
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

#ifdef __cplusplus
}
#endif

#endif /* PMP_H */