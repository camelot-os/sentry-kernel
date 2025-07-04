// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive. should never be used directly,
 *          use <sentry/io.h> instead
 *
 * NOTE: in Frama-C mode, these API is not traversed as it contains only ASM
 */

#ifndef __ASM_IO_H
#define __ASM_IO_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>
#include <inttypes.h>

#ifndef IO_H
#error "must not be included directly, used sentry/io.h instead"
#endif


/**
 * @brief  RV32 asm implementation of iowrite8
 *
 * @param addr destination address
 * @param val byte to write
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void __iowrite8(size_t addr, uint8_t val)
{
    asm volatile(
        "sb %1, %0" : : "Qo" (*(volatile uint8_t *)addr), "r" (val) : "memory"
    );
}

/**
 * @brief  RV32 asm implementation of iowrite16
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
        "sh %1, %0" : : "Qo" (*(volatile uint16_t *)addr), "r" (val) : "memory"
    );
}

/**
 * @brief  RV32 asm implementation of iowrite32
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
    *(uint32_t*)addr = val;
}

/**
 * @brief  RV32 asm implementation of ioread8
 *
 * @param addr source address
 * @return readden byte
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint8_t __ioread8(size_t addr)
{
    uint8_t val;

    asm volatile("lbu %0, 0(%1)" : "=r" (val) : "r" (addr));

    return val;
}

/**
 * @brief  RV32 asm implementation of ioread16
 *
 * @param addr source address
 * @return readden half-word
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint16_t __ioread16(size_t addr)
{
    uint16_t val;

    asm volatile("lhu %0, 0(%1)" : "=r" (val) : "r" (addr));

    return val;
}

/**
 * @brief  RV32 asm implementation of ioread32
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

    asm volatile ("lw %0, 0(%1)"  : "=r"(val) : "r" (addr));

    return val;
}

#ifdef __cplusplus
}
#endif

#endif /* __ASM_IO_H */
