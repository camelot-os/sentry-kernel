// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef PMP_H
#define PMP_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

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

#endif /* PMP_H */