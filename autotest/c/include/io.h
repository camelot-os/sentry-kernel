// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef IO_H
#define IO_H

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>

#if defined(__arm__)
#include <arch/asm-cortex-m/io.h>
#elif defined(CONFIG_ARCH_RV32)
#include <arch/asm-rv32/io.h>
#else
#error "unsupported architecture"
#endif


/**
 * @brief  Writes a word at given address
 *
 * @param addr destination address
 * @param val word to write
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void iowrite32(size_t addr, uint32_t val)
{
    __iowrite32(addr, val);
}

/**
 * @brief  Writes a halfword at given address
 *
 * @param addr destination address
 * @param val word to write
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void iowrite16(size_t addr, uint16_t val)
{
    __iowrite16(addr, val);
}

/**
 * @brief  Reads a word from given address
 *
 * @param addr source address
 * @return readden word
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint32_t ioread32(size_t addr)
{
    return __ioread32(addr);
}


#endif
