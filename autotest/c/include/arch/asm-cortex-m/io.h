// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive. should never be used directly, use <sentry/io.h instead
 *
 * NOTE: in Frama-C mode, these API is not traversed as it contains only ASM
 */

#ifndef __ASM_IO_H
#define __ASM_IO_H

#include <stddef.h>
#include <inttypes.h>

#ifndef IO_H
#error "must not be included directly, used sentry/io.h instead"
#endif


/**
 * @brief  ARM asm implementation of iowrite32
 *
 * @param addr destination address
 * @param val word to write
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void __iowrite32(size_t addr, uint32_t val)
{
    asm volatile(
        "str %1, %0" : : "Qo" (*(volatile uint32_t *)addr), "r" (val) : "memory"
    );
}

/**
 * @brief  ARM asm implementation of iowrite16
 *
 * @param addr destination address
 * @param val half-word to write
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void __iowrite16(size_t addr, uint16_t val)
{
    asm volatile(
        "strh %1, %0" : : "Qo" (*(volatile uint16_t *)addr), "r" (val) : "memory"
    );

}

/**
 * @brief  ARM asm implementation of ioread32
 *
 * @param addr source address
 * @return readden word
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint32_t __ioread32(size_t addr)
{
    uint32_t val;

    asm volatile(
        "ldr %0, %1" : "=r" (val) : "Qo" (*(volatile uint32_t *)addr) : "memory"
    );

    return val;
}

#endif
