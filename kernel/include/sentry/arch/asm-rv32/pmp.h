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

#include <sentry/managers/memory_types.h>

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

#define TASK_FIRST_REGION_NUMBER 2
#define TASK_MAX_RESSOURCES_NUM (CONFIG_NUM_MPU_REGIONS)

#include <sentry/managers/memory.h>

#define CSR_PMPCFG_BASE  0x3a0
#define CSR_PMPADDR_BASE 0x3b0

#define PMP_NAPOT_MODE 0x03

#define NAPOT_base(addr) (addr & (addr + 1))
#define NAPOT_end(addr) (addr | (addr + 1))

#define PMPCFG_GET(pmpcfg, index) (pmpcfg >> (index *8))
#define PMPCFG_GET_R(pmpcfg) (pmpcfg & 1)
#define PMPCFG_SET_R(pmpcfg) (pmpcfg |= 1)
#define PMPCFG_GET_W(pmpcfg) ((pmpcfg >> 1) & 1)
#define PMPCFG_SET_W(pmpcfg) (pmpcfg |= (1 << 1))
#define PMPCFG_GET_X(pmpcfg) ((pmpcfg >> 2) & 1)
#define PMPCFG_SET_X(pmpcfg) (pmpcfg |= (1 << 2))
#define PMPCFG_GET_A(pmpcfg) ((pmpcfg >> 3) & 3)
#define PMPCFG_SET_A(pmpcfg, mode) \
    (pmpcfg = ((pmpcfg & ~(0x03 << 3)) | ((mode & 0x03) << 3)))
#define PMPCFG_GET_L(pmpcfg) ((pmpcfg >> 6) & 1)
#define PMPCFG_SET_L(pmpcfg) (pmpcfg |= (1 << 6))
#define PMPCFG_SET_CONF(pmpcfg, index, value) \
    (pmpcfg = ((pmpcfg & ~(0xff << (index * 8))) | ((value & 0xff) << index)))

#define _WRITE_PMPCFG(REG, VALUE) CSR_WRITE_ADDR(REG, VALUE)
#define WRITE_PMPCFG(REG, VALUE) _WRITE_PMPCFG((CSR_PMPCFG_BASE + REG), VALUE)
#define _READ_PMPCFG(REG) CSR_READ_ADDR(REG)
#define READ_PMPCFG(REG) _READ_PMPCFG((CSR_PMPCFG_BASE + REG))

#define _WRITE_PMPADDR(REG, VALUE) CSR_WRITE_ADDR(REG, VALUE >> 2)
#define WRITE_PMPADDR(REG, VALUE) _WRITE_PMPADDR((CSR_PMPADDR_BASE + REG), VALUE)
#define _READ_PMPADDR(REG) (CSR_READ_ADDR(REG) << 2)
#define READ_PMPADDR(REG) _READ_PMPADDR((CSR_PMPADDR_BASE + REG))

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

static inline void _write_pmpcfg(uint8_t reg, uint32_t value)
{
  switch (reg)
  {
  case 0: WRITE_PMPCFG(0, value); break;
  case 1: WRITE_PMPCFG(1, value); break;
#if CONFIG_NUM_MPU_REGIONS >= 16
  case 2: WRITE_PMPCFG(2, value); break;
  case 3: WRITE_PMPCFG(3, value); break;
#endif
#if CONFIG_NUM_MPU_REGIONS >= 32
  case 4: WRITE_PMPCFG(4, value); break;
  case 5: WRITE_PMPCFG(5, value); break;
  case 6: WRITE_PMPCFG(6, value); break;
  case 7: WRITE_PMPCFG(7, value); break;
  case 8: WRITE_PMPCFG(8, value); break;
#endif
#if CONFIG_NUM_MPU_REGIONS >= 64
  case 9: WRITE_PMPCFG(9, value); break;
  case 10: WRITE_PMPCFG(10, value); break;
  case 11: WRITE_PMPCFG(11, value); break;
  case 12: WRITE_PMPCFG(12, value); break;
  case 13: WRITE_PMPCFG(13, value); break;
  case 14: WRITE_PMPCFG(14, value); break;
  case 15: WRITE_PMPCFG(15, value); break;
#endif
  }
}

static inline uint32_t _read_pmpcfg(uint8_t reg)
{
  switch (reg)
  {
  case 0: return READ_PMPCFG(0);
  case 1: return READ_PMPCFG(1);
#if CONFIG_NUM_MPU_REGIONS >= 16
  case 2: return READ_PMPCFG(2);;
  case 3: return READ_PMPCFG(3);;
#endif
#if CONFIG_NUM_MPU_REGIONS >= 32
  case 4: return READ_PMPCFG(4);
  case 5: return READ_PMPCFG(5);
  case 6: return READ_PMPCFG(6);
  case 7: return READ_PMPCFG(7);
  case 8: return READ_PMPCFG(8);
#endif
#if CONFIG_NUM_MPU_REGIONS >= 64
  case 9: return READ_PMPCFG(9);
  case 10: return READ_PMPCFG(10);
  case 11: return READ_PMPCFG(11);
  case 12: return READ_PMPCFG(12);
  case 13: return READ_PMPCFG(13);
  case 14: return READ_PMPCFG(14);
  case 15: return READ_PMPCFG(15);
#endif
  }

  // TODO: assert false
  return 0;
}

static inline void _write_pmpaddr(uint8_t reg, uint32_t value)
{
  switch (reg)
  {
  case 0: WRITE_PMPADDR(0, value); break;
  case 1: WRITE_PMPADDR(1, value); break;
  case 2: WRITE_PMPADDR(2, value); break;
  case 3: WRITE_PMPADDR(3, value); break;
  case 4: WRITE_PMPADDR(4, value); break;
  case 5: WRITE_PMPADDR(5, value); break;
  case 6: WRITE_PMPADDR(6, value); break;
  case 7: WRITE_PMPADDR(7, value); break;
  case 8: WRITE_PMPADDR(8, value); break;
#if CONFIG_NUM_MPU_REGIONS >= 16
  case 9: WRITE_PMPADDR(9, value); break;
  case 10: WRITE_PMPADDR(10, value); break;
  case 11: WRITE_PMPADDR(11, value); break;
  case 12: WRITE_PMPADDR(12, value); break;
  case 13: WRITE_PMPADDR(13, value); break;
  case 14: WRITE_PMPADDR(14, value); break;
  case 15: WRITE_PMPADDR(15, value); break;
#endif
#if CONFIG_NUM_MPU_REGIONS >= 32
  case 16: WRITE_PMPADDR(16, value); break;
  case 17: WRITE_PMPADDR(17, value); break;
  case 18: WRITE_PMPADDR(18, value); break;
  case 19: WRITE_PMPADDR(19, value); break;
  case 20: WRITE_PMPADDR(20, value); break;
  case 21: WRITE_PMPADDR(21, value); break;
  case 22: WRITE_PMPADDR(22, value); break;
  case 23: WRITE_PMPADDR(23, value); break;
  case 24: WRITE_PMPADDR(24, value); break;
  case 25: WRITE_PMPADDR(25, value); break;
  case 26: WRITE_PMPADDR(26, value); break;
  case 27: WRITE_PMPADDR(27, value); break;
  case 28: WRITE_PMPADDR(28, value); break;
  case 29: WRITE_PMPADDR(29, value); break;
  case 30: WRITE_PMPADDR(30, value); break;
  case 31: WRITE_PMPADDR(31, value); break;
#endif
#if CONFIG_NUM_MPU_REGIONS >= 64
  case 32: WRITE_PMPADDR(32, value); break;
  case 33: WRITE_PMPADDR(33, value); break;
  case 34: WRITE_PMPADDR(34, value); break;
  case 35: WRITE_PMPADDR(35, value); break;
  case 36: WRITE_PMPADDR(36, value); break;
  case 37: WRITE_PMPADDR(37, value); break;
  case 38: WRITE_PMPADDR(38, value); break;
  case 39: WRITE_PMPADDR(39, value); break;
  case 40: WRITE_PMPADDR(40, value); break;
  case 41: WRITE_PMPADDR(41, value); break;
  case 42: WRITE_PMPADDR(42, value); break;
  case 43: WRITE_PMPADDR(43, value); break;
  case 44: WRITE_PMPADDR(44, value); break;
  case 45: WRITE_PMPADDR(45, value); break;
  case 46: WRITE_PMPADDR(46, value); break;
  case 47: WRITE_PMPADDR(47, value); break;
  case 48: WRITE_PMPADDR(48, value); break;
  case 49: WRITE_PMPADDR(49, value); break;
  case 50: WRITE_PMPADDR(50, value); break;
  case 51: WRITE_PMPADDR(51, value); break;
  case 52: WRITE_PMPADDR(52, value); break;
  case 53: WRITE_PMPADDR(53, value); break;
  case 54: WRITE_PMPADDR(54, value); break;
  case 55: WRITE_PMPADDR(55, value); break;
  case 56: WRITE_PMPADDR(56, value); break;
  case 57: WRITE_PMPADDR(57, value); break;
  case 58: WRITE_PMPADDR(58, value); break;
  case 59: WRITE_PMPADDR(59, value); break;
  case 60: WRITE_PMPADDR(60, value); break;
  case 61: WRITE_PMPADDR(61, value); break;
  case 62: WRITE_PMPADDR(62, value); break;
  case 63: WRITE_PMPADDR(63, value); break;
  case 64: WRITE_PMPADDR(64, value); break;
#endif
  }
}

static inline uint32_t _read_pmpaddr(uint8_t reg)
{
  switch (reg)
  {
  case 0: return READ_PMPADDR(0);
  case 1: return READ_PMPADDR(1);
  case 2: return READ_PMPADDR(2);
  case 3: return READ_PMPADDR(3);
  case 4: return READ_PMPADDR(4);
  case 5: return READ_PMPADDR(5);
  case 6: return READ_PMPADDR(6);
  case 7: return READ_PMPADDR(7);
  case 8: return READ_PMPADDR(8);
#if CONFIG_NUM_MPU_REGIONS >= 16
  case 9: return READ_PMPADDR(9);
  case 10: return READ_PMPADDR(10);
  case 11: return READ_PMPADDR(11);
  case 12: return READ_PMPADDR(12);
  case 13: return READ_PMPADDR(13);
  case 14: return READ_PMPADDR(14);
  case 15: return READ_PMPADDR(15);
#endif
#if CONFIG_NUM_MPU_REGIONS >= 32
  case 16: return READ_PMPADDR(16);
  case 17: return READ_PMPADDR(17);
  case 18: return READ_PMPADDR(18);
  case 19: return READ_PMPADDR(19);
  case 20: return READ_PMPADDR(20);
  case 21: return READ_PMPADDR(21);
  case 22: return READ_PMPADDR(22);
  case 23: return READ_PMPADDR(23);
  case 24: return READ_PMPADDR(24);
  case 25: return READ_PMPADDR(25);
  case 26: return READ_PMPADDR(26);
  case 27: return READ_PMPADDR(27);
  case 28: return READ_PMPADDR(28);
  case 29: return READ_PMPADDR(29);
  case 30: return READ_PMPADDR(30);
  case 31: return READ_PMPADDR(31);
#endif
#if CONFIG_NUM_MPU_REGIONS >= 64
  case 32: return READ_PMPADDR(32);
  case 33: return READ_PMPADDR(33);
  case 34: return READ_PMPADDR(34);
  case 35: return READ_PMPADDR(35);
  case 36: return READ_PMPADDR(36);
  case 37: return READ_PMPADDR(37);
  case 38: return READ_PMPADDR(38);
  case 39: return READ_PMPADDR(39);
  case 40: return READ_PMPADDR(40);
  case 41: return READ_PMPADDR(41);
  case 42: return READ_PMPADDR(42);
  case 43: return READ_PMPADDR(43);
  case 44: return READ_PMPADDR(44);
  case 45: return READ_PMPADDR(45);
  case 46: return READ_PMPADDR(46);
  case 47: return READ_PMPADDR(47);
  case 48: return READ_PMPADDR(48);
  case 49: return READ_PMPADDR(49);
  case 50: return READ_PMPADDR(50);
  case 51: return READ_PMPADDR(51);
  case 52: return READ_PMPADDR(52);
  case 53: return READ_PMPADDR(53);
  case 54: return READ_PMPADDR(54);
  case 55: return READ_PMPADDR(55);
  case 56: return READ_PMPADDR(56);
  case 57: return READ_PMPADDR(57);
  case 58: return READ_PMPADDR(58);
  case 59: return READ_PMPADDR(59);
  case 60: return READ_PMPADDR(60);
  case 61: return READ_PMPADDR(61);
  case 62: return READ_PMPADDR(62);
  case 63: return READ_PMPADDR(63);
  case 64: return READ_PMPADDR(64);
#endif
  }
  /// TODO assert false
  return 0;
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

  _write_pmpcfg(0, 0);
  _write_pmpaddr(0, 0xffffffff);
  addr = _read_pmpaddr(0);

  while (((addr >> i) & 1) == 0) {
    i += 1;
  }

  return (1 << (i + 2));
}

/**
 * @brief Set a PMP configuration
 */
static inline void __mpu_set_region(const layout_resource_t *resource)
{
  uint32_t pmpcfg;
  uint8_t pmpcfg_num = resource[0].index/4;
  uint8_t pmpcfg_ind = resource[0].index%4;

  _write_pmpaddr(resource[0].index, resource[0].pmpaddr);

  pmpcfg = _read_pmpcfg(pmpcfg_num);

  PMPCFG_SET_CONF(pmpcfg, pmpcfg_ind, resource[0].pmpcfg);

  _write_pmpcfg(pmpcfg_num, pmpcfg);
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

static inline uint32_t _pmp_convert_napot(uint32_t addr, uint32_t size)
{
  if (0 != (addr % size)) {
    return 0;
  } else {
    return addr | ((size - 1) >> 1);
  }
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
      pmpcfg = _read_pmpcfg((index/4));
    }

    if (0 == PMPCFG_GET_A(PMPCFG_GET(pmpcfg, index%4))) {
      // Region not assigned yet
      break;
    }

    index++;
  }

  if (NB_PMP_REGIONS == index) {
    // No free region has been found
    return K_ERROR_BADSTATE;
  }

  resource->index = index;
  if (0 == (resource->pmpaddr = _pmp_convert_napot(desc->addr, desc->size))) {
    return K_ERROR_BADSTATE;
  }

  resource->pmpcfg = 0;

  // For simplicity, always use NAPOT
  PMPCFG_SET_A(resource->pmpcfg, PMP_NAPOT_MODE);

  switch (desc->access_perm) {
  case MPU_REGION_PERM_FULL:
  case MPU_REGION_PERM_PRIV:
    PMPCFG_SET_R(resource->pmpcfg);
    PMPCFG_SET_W(resource->pmpcfg);
    break;
  case MPU_REGION_PERM_RO:
  case MPU_REGION_PERM_PRIV_RO:
    PMPCFG_SET_R(resource->pmpcfg);
    break;
  default:
    /* Should not happen */
    return K_ERROR_INVPARAM;
  }

  if (false == desc->noexec) {
    PMPCFG_SET_X(resource->pmpcfg);
  }

  status = K_STATUS_OKAY;
  /*@ assert (status == K_STATUS_OKAY); */
  return status;
}

/**
 * @brief RISC-V PMP activate memory region control
 *
 * @param first_region_number First index to be loaded
 * @param resource            Resource layout table
 * @param num_resources       Number of resources to activate
 */
/*@
  requires \valid_read(resource + (0 .. num_resources-1));
  requires ((first_region_number + num_resources) <= CONFIG_NUM_MPU_REGIONS);
 */
static inline void __mpu_fastload(
    uint32_t first_region_number,
    const layout_resource_t *resource,
    uint8_t num_resources)
{
  uint8_t i = 0;
  uint32_t pmpcfg;
  uint8_t pmpcfg_num;
  uint8_t pmpcfg_ind;

  for (i = 0; i < num_resources; i++) {
    _write_pmpaddr(resource[i].index, resource[i].pmpaddr);

    pmpcfg_num = resource[i].index/4;
    pmpcfg_ind = resource[i].index%4;

    pmpcfg = _read_pmpcfg(pmpcfg_num);
    PMPCFG_SET_CONF(pmpcfg, pmpcfg_ind, resource[i].pmpcfg);
    _write_pmpcfg(pmpcfg_num, pmpcfg);
  }
}

/**
 * @brief Load memory region description table in MPU
 *
 * @note On RISC-V without the Smepmp extension the PMP cannot enforce access
 *        on M-mode without locking the region until the next reset.
 *        Thus on core without the Smepmp extension "MM_REGION_KERNEL_TXT" sections
 *        are ignored by the PMP.
 */
static inline kstatus_t mpu_load_descriptors(
    const struct mpu_region_desc *region_descs,
    size_t count)
{
  kstatus_t status = K_ERROR_INVPARAM;
  const struct mpu_region_desc *desc = NULL;
  layout_resource_t resource;
  /*@ assert \valid_read(region_descs); */

  // TODO: add fence

  for (size_t i = 0UL; i < count; i++) {
    desc = region_descs + i;

    if (MM_REGION_KERNEL_TXT == desc->id) {
      continue;
    }

    mpu_forge_resource(desc, &resource);
    __mpu_set_region(&resource);
  }

  // TODO: add fence

  status = K_STATUS_OKAY;
  /*@ assert(status == K_STATUS_OKAY); */
  return status;
}

/**
 * @brief Create empty resource layout
 */
static inline kstatus_t mpu_forge_unmapped_ressource(uint8_t id, layout_resource_t *resource)
{
  kstatus_t status = K_ERROR_INVPARAM;

  resource->index = 0;
  resource->pmpaddr = 0;
  resource->pmpcfg = 0;

  status = K_STATUS_OKAY;

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
  uint32_t pmpcfg;
  uint32_t pmpaddr;

  /*@
    loop invariant 0 <= i <= num_resources;
    loop assigns *id, status;
    loop assigns resource;
    loop variant (num_resources - i);
   */
  for (uint8_t i = 0; i < num_resources; ++i) {
    pmpcfg = _read_pmpcfg(resource[0].index/4);
    pmpaddr = _read_pmpaddr(resource[0].index);

    if ((PMP_NAPOT_MODE == PMPCFG_GET_A(pmpcfg)) &&
        (addr >= NAPOT_base(pmpaddr)) &&
        (addr <= NAPOT_end(pmpaddr))) {
      // TODO: check offset
      *id = i + TASK_FIRST_REGION_NUMBER;
      status = K_STATUS_OKAY;
      break;
    }

    resource++;
  }

  return status;
}

/*@
   requires \valid_read(resource);
   assigns \nothing;
 */
static inline secure_bool_t __pmp_is_resource_free(const layout_resource_t *resource)
{
  secure_bool_t is_free = SECURE_FALSE;

  uint32_t pmpcfg = _read_pmpcfg(resource[0].index/4);
  if (0 == PMPCFG_GET_A(PMPCFG_GET(pmpcfg, resource[0].index%4))) {
    is_free = SECURE_TRUE;
  }

  return is_free;
}

/*@
  requires \valid(id);
  requires (num_resources < CONFIG_NUM_MPU_REGIONS);
  requires \valid_read(resource + (0 .. num_resources - 1));
  assigns *id;
 */
#ifndef CONFIG_BUILD_TARGET_AUTOTEST
static inline
#else
static
#endif
    kstatus_t
    mpu_get_free_id(const layout_resource_t *resource, uint8_t num_resources, uint8_t *id)
{
  kstatus_t status = K_ERROR_NOENT;
  uint32_t pmpcfg = 0;

  // Find available PMP region
  /*@
    loop invariant 0 <= i <= num_resources;
    loop assigns *id, status;
    loop assigns resource;
    loop variant (num_resources - i);
   */
  for (uint8_t i = 0; i < num_resources; ++i) {
    if (SECURE_TRUE == __pmp_is_resource_free(resource)) {
      // Region not assigned yet
      *id = i;
      status = K_STATUS_OKAY;
      break;
    }
    resource++;
  }

  return status;
}

static inline void mpu_clear_region(uint32_t rnr)
{
  _mpu_initialize();
}

#ifdef __cplusplus
}
#endif

#endif /* PMP_H */