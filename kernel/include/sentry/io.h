// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef IO_H
#define IO_H

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stddef.h>
#include <assert.h>
#include <stdbool.h>

/* dispatcher for I/O file based on compiler host value */
#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/io.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/io.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/io.h>
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/io.h>
#else
#error "unsupported architecture"
#endif

#include <sentry/ktypes.h>

#if defined(__cplusplus)
extern "C" {
#endif

#ifndef __cplusplus
#if defined(__arm__)
/** @brief Generic iowrite interface that implicitely handle multiple sizes */
#define iowrite(reg, T) _Generic((T),   \
              size_t:   iowrite32,      \
              uint32_t: iowrite32,      \
              uint16_t: iowrite16,      \
              uint8_t:  iowrite8        \
        ) (reg, T)
#elif defined(__i386__)
/** @brief generic interface for FramaC analysis (x86_32)
  *
  * INFO: on x86_32 arch (framaC, size_t & uint32_t are the same and thus
  *  can't be both declared).
  * In the same time, long & u32 are not the same
  */
#define iowrite(reg, T) _Generic((T),   \
              unsigned long: iowrite32, \
              uint32_t: iowrite32,      \
              uint16_t: iowrite16,      \
              uint8_t:  iowrite8        \
        ) (reg, T)
#elif defined(__x86_64__)
/** @brief generic interface for unit testing (x86_32)
  *
  * INFO: on x86_32 arch (framaC, size_t & uint32_t are the same and thus
  *  can't be both declared).
  * In the same time, long & u32 are not the same
  */
#define iowrite(reg, T) _Generic((T),   \
              size_t:   iowrite32,      \
              uint32_t: iowrite32,      \
              uint16_t: iowrite16,      \
              uint8_t:  iowrite8        \
        ) (reg, T)
#elif defined(CONFIG_ARCH_RV32)
/** @brief Generic iowrite interface that implicitely handle multiple sizes */
#define iowrite(reg, T) _Generic((T),   \
              size_t:   iowrite32,      \
              uint32_t: iowrite32,      \
              uint16_t: iowrite16,      \
              uint8_t:  iowrite8        \
        ) (reg, T)
#else
#error "unsupported architecture"
#endif

#endif/*!__cplusplus*/

/**
 * @brief  Writes one byte at given address
 *
 * @param addr destination address
 * @param val byte to write
 *
 * @note this function is always inline
 */
/*@
  assigns *(uint8_t*)addr;
*/
__attribute__((always_inline))
static inline void iowrite8(size_t addr, uint8_t val)
{
#ifdef __FRAMAC__
    *(uint8_t*)addr = val;
#else
    __iowrite8(addr, val);
#endif
}

/**
 * @brief  Writes an half-word at given address
 *
 * @param addr destination address
 * @param val half-word to write
 *
 * @note this function is always inline
 */
/*@
  assigns *(uint16_t*)addr;
*/
__attribute__((always_inline))
static inline void iowrite16(size_t addr, uint16_t val)
{
#ifdef __FRAMAC__
    *(uint16_t*)addr = val;
#else
    __iowrite16(addr, val);
#endif
}

/**
 * @brief  Writes a word at given address
 *
 * @param addr destination address
 * @param val word to write
 *
 * @note this function is always inline
 */
/*@
  assigns *(uint32_t*)addr;
*/
__attribute__((always_inline))
static inline void iowrite32(size_t addr, uint32_t val)
{
#ifdef __FRAMAC__
    *(uint32_t*)addr = val;
#else
    __iowrite32(addr, val);
#endif
}

/**
 * @brief  Reads one byte from given address
 *
 * @param addr source address
 * @return readden byte
 *
 * @note this function is always inline
 */
/*@
  assigns \nothing;
*/
__attribute__((always_inline))
static inline uint8_t ioread8(size_t addr)
{
#ifdef __FRAMAC__
    return *(uint8_t*)addr;
#else
    return __ioread8(addr);
#endif
}

/**
 * @brief  Reads an half-word from given address
 *
 * @param addr source address
 * @return readden half-word
 *
 * @note this function is always inline
 */
/*@
  assigns \nothing;
*/
__attribute__((always_inline))
static inline uint16_t ioread16(size_t addr)
{
#ifdef __FRAMAC__
    return *(uint16_t*)addr;
#else
    return __ioread16(addr);
#endif
}

/**
 * @brief  Reads a word from given address
 *
 * @param addr source address
 * @return readden word
 *
 * @note this function is always inline
 */
/*@
  assigns \nothing;
*/
__attribute__((always_inline))
static inline uint32_t ioread32(size_t addr)
{
#ifdef __FRAMAC__
    return *(uint32_t*)addr;
#else
    return __ioread32(addr);
#endif
}

/**
 * @brief poll register until all bits in bitmask are set
 *
 * @param addr register address
 * @param bitmask bitmask to wait for
 * @param nretry maximum number of try
 *
 * @return K_STATUS_OKAY once bitfield is set, K_ERROR_NOTREADY if nretry is reached
 * without bitfield equality.
 */
static inline kstatus_t iopoll32_until_set(size_t addr, uint32_t bitmask, uint32_t nretry)
{
    kstatus_t status = K_STATUS_OKAY;
    uint32_t count = 0UL;
    uint32_t bitfield;

    do {
        bitfield = ioread32(addr) & bitmask;
        count++;
    } while ((bitfield != bitmask) && (count < nretry));

    if (unlikely(bitfield != bitmask)) {
        status = K_ERROR_NOTREADY;
    }

    return status;
}

#if defined(__cplusplus)
}
#endif

#endif /* IO_H */
