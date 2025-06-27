// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef MEMORY_TYPES_H
#define MEMORY_TYPES_H

#if defined(__cplusplus)
extern "C" {
#endif

typedef enum mm_k_region {
    MM_REGION_KERNEL_TXT = 0, /* starting point of userspace ressources */
    MM_REGION_KERNEL_DATA = 1,
    MM_REGION_KERNEL_DEVICE = CONFIG_NUM_MPU_REGIONS - 1,
} mm_k_region_t;

#if defined(__cplusplus)
}
#endif

#endif/*!MEMORY_TYPES_H*/