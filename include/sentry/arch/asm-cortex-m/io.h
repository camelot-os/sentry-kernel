// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef __ASM_IO_H
#define __ASM_IO_H

#include <stddef.h>
#include <inttypes.h>

#ifndef IO_H
#error "must not be included directly, used ssol/io.h instead"
#endif

/**
 * @brief  ARM asm implementation of iowrite8
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
        "strb %1, %0" : : "Qo" (*(volatile uint8_t *)addr), "r" (val) : "memory"
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
 *
 * @warning this may be problematic prior to ARMv6 architecture
 */
__attribute__((always_inline))
static inline void __iowrite16(size_t addr, uint16_t val)
{
    asm volatile(
        "strh %1, %0" : : "Qo" (*(volatile uint16_t *)addr), "r" (val) : "memory"
    );
}

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
 * @brief  ARM asm implementation of ioread8
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

    asm volatile(
        "ldrb %0, %1" : "=r" (val) : "Qo" (*(volatile uint8_t *)addr) : "memory"
    );

    return val;
}

/**
 * @brief  ARM asm implementation of ioread16
 *
 * @param addr source address
 * @return readden half-word
 *
 * @note there is a compiler barrier in order to prevent compiler to reorder memory access.
 *
 * @note this function is always inline
 *
 * @warning this may be problematic prior to ARMv6 architecture
 */
__attribute__((always_inline))
static inline uint16_t __ioread16(size_t addr)
{
    uint16_t val;

    asm volatile(
        "ldrh %0, %1" : "=r" (val) : "Qo" (*(volatile uint16_t *)addr) : "memory"
    );

    return val;
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

#endif /* __ASM_IO_H */
