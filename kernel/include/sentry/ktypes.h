// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef KTYPES_H
#define KTYPES_H

/**
 * \file sentry kernel generic types
 */
#include <sentry/zlib/compiler.h>

/*
 * INFO: the way atomics are manipulated is not the same in C (kernel build)
 * and C++ (unit testing). This is transparent for all the caller code but the
 * atomic types definitions and model is not the same and thus require to
 * detect the context of this header (c++ ABI vs c ABI)
 */
#if defined(__cplusplus)
  #include <atomic>
  using std::atomic_int;
  using std::memory_order;
  using std::memory_order_acquire;
#else /* not __cplusplus */
  #include <stdatomic.h>
#endif /* defined(__cplusplus) */

#include <assert.h>
#include <inttypes.h>

#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

typedef enum secure_bool {
    SECURE_TRUE   = 0x5aa33FFu,
    SECURE_FALSE  = 0xa55FF33u
} secure_bool_t;

/*
 * TODO, other suffix Kilo, Mega, Giga in decimal
 * be careful, the official units prefixes are (since 2008 !):
 *  - k = 1000
 *  - Ki = 1024
 *  - M = 1000 * 1000
 *  - Mi = 1024 * 1024
 * and so on.
 * see IEC 80000 standard.
 *
 * The confusion comes from memory drive manufacturer which used ISO prefixes for memory size instead of power of 2
 */
#define KBYTE 1024u
#define MBYTE (1024u*1024u)
#define GBYTE (1024u*1024u*1024u)

#define KILO 1000UL
#define MEGA (1000UL * KILO)
#define GIGA (1000UL * MEGA)

#define MSEC_PER_SEC 1000UL
#define USEC_PER_SEC 1000000UL

/*
 * sanity check at build time.
 * As atomic bool are used from irq context, it **MUST BE** lock free for our usage.
 */
static_assert(ATOMIC_BOOL_LOCK_FREE, "Atomic boolean needs to be lock free");

#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

/**
 * @def ARRAY_SIZE(x)
 * @brief Helper to return an array size
 *
 * use only with **statically** sized `c` array.
 *
 * @warning According to sizeof specification:
 * @warning  - Do not use w/ zero-sized or flexible array (those are incomplete types)
 *
 * @warning Do not use w/ array decayed to pointer nor raw pointer
 * @warning Array size must be preserved on different architecture and sizeof(ptr)
 * @warning is architecture dependent
 */
#define ARRAY_SIZE(x) (sizeof(x) / sizeof(x[0]))

/**
 * from a given array base address and cell pointer, return the cell index in the array
 * @warning the cell pointer must be part of the array, otherwise the behavior is undefined
 * @warning the array must be statically sized, otherwise the behavior is undefined
 * @warning the array size must be preserved on different architecture and sizeof(ptr) is architecture dependent
 */
#define ARRAY_CELL_INDEX(base, cell) (((uintptr_t)(cell) - (uintptr_t)(base)) / sizeof((base)[0]))
/**
 * @note volatile usage is deprecated and must limited as much as possible
 * Plus, the assumption of 4 bytes register is false (some IPs got 8 bits registers)
 * consider adding ioreadX/iowriteX functions.
 *  - for cortex m, this may be an asm ld, str with compiler barrier
 *  - for cortex a, this may requires a dmb (data memory barrier) in addition
 * In order to produce portable driver this is mandatory as ioread/write may use specific
 * intrinsics.
 */
#define REG_ADDR(addr)      ((volatile uint32_t *)(addr))

/*
 * XXX:
 * May be we should defined a more robust time definition.
 * This is also based on the fact that systick is set to one ms.
 * Do not mix resolution and precision for measurements.
 * e.g. the time resolution may be milliseconds
 */
typedef unsigned long long  time_ms_t;

/**
 * @brief Helper that checks value range
 *
 * @param x scalar value to check
 * @param m range lower bound (included)
 * @param M range upper bound (included)
 *
 * @return True is `x` is in range [`m`..`M`]
 */
#define __IN_RANGE(x, m, M) (((x) >= m) && ((x) <= M))

/**
 * @brief Helper that checks value range
 *
 * @param x scalar value to check
 * @param R scalar value range define w/ @def RANGE
 */
#define IN_RANGE(x, R) __IN_RANGE(x,R)

#define __RANGE(m,M) (m),(M)
#define RANGE(m,M) __RANGE(m,M)

typedef enum kstatus {
    K_STATUS_OKAY = 0,
    K_ERROR_BUSY,
    K_ERROR_INVPARAM,
    K_ERROR_BADSTATE,
    K_ERROR_UNKNOWN,
    K_ERROR_BADCLK,
    K_ERROR_BADENTROPY,
    K_ERROR_NOTREADY,
    K_ERROR_NOENT,
    K_ERROR_MEMFAIL,
    K_ERROR_DENIED,
    K_SECURITY_INVSTATE,
    K_SECURITY_CORRUPTION,
    K_SECURITY_LOCKDOWN,
    K_SECURITY_FIPSCOMPLIANCE,
    K_SECURITY_INTEGRITY,
} kstatus_t;

#if defined(__cplusplus)
} /* extern "C" */
#endif

#endif /* KTYPES_H */
