// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef LIBTEST_ASSERT_H
#define LIBTEST_ASSERT_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file assert.h
 *
 * testlib assertion API to compare and pretty-print various checks.
 * based on the #ASSERT() macro to handle the pretty print mechanism.
 *
 * See \file log.h for pretty print mechanism.
 */

#include <stdio.h>
#include <test_log.h>

#define __IN_RANGE(x, m, M) (((x) >= m) && ((x) <= M))

/**
 * @def ASSERT
 *
 * assert that expr holding two comparative element a and b is true.
 * If yes, print a success message holding 'a successcmp b' (e.g. 0 == 0),
 * If no, print a failure message holding 'a failcmp b' (e.g. 0 != 1)
 * the log prefix mechanism is automatically added so that it can be grepped
 * in the log output easily
 */
#define ASSERT(expr,failcmp, successcmp, a, b) ({do {   \
    if (!(expr))                                        \
        failure(__func__, __LINE__, failcmp, a, b);     \
    else                                                \
        success(__func__, __LINE__, successcmp, a, b);  \
} while (0);})


/**
 * @def ASSERT_EQ
 *
 * assert that a and b are equal. b is considered are type-equivalent to b
 * and numerical. Multiple types are supported (u32, u64, int, Status...)
 */
#define ASSERT_EQ(a,b) (ASSERT((a) == (b), "!=", "==", a, (typeof(a))b))

/**
 * @def ASSERT_NE
 *
 * assert that a and b are different. b is considered are type-equivalent to b
 * and numerical. Multiple types are supported (u32, u64, int, Status...)
 */
#define ASSERT_NE(a,b) (ASSERT((a) != (b), "==", "!=", a, (typeof(a))b))

/**
 * @def ASSERT_GT
 *
 * assert that a is stricly bigger than b. b is considered are type-equivalent to b
 * and numerical. Multiple types are supported (u32, u64, int, Status...)
 */
#define ASSERT_GT(a,b) (ASSERT((a) > (b), "<=", ">", a, (typeof(a))b))

/**
 * @def ASSERT_GE
 *
 * assert that a is bigger or equal to b. b is considered are type-equivalent to b
 * and numerical. Multiple types are supported (u32, u64, int, Status...)
 */
#define ASSERT_GE(a,b) (ASSERT((a) >= (b), "<", ">=", a, (typeof(a))b))

/**
 * @def ASSERT_LT
 *
 * assert that a is stricly smaller than b. b is considered are type-equivalent to b
 * and numerical. Multiple types are supported (u32, u64, int, Status...)
 */
#define ASSERT_LT(a,b) (ASSERT((a) < (b), ">=", "<", a, (typeof(a))b))

/**
 * @def ASSERT_LT
 *
 * assert that a is smalloer or equal to b. b is considered are type-equivalent to b
 * and numerical. Multiple types are supported (u32, u64, int, Status...)
 */
#define ASSERT_LE(a,b) (ASSERT((a) <= (b), ">", "<=", a, (typeof(a))b))

#define ASSERT_IN_RANGE(a,b,B) ({          \
 do {                                      \
    LOG("Range assertion");                \
    ASSERT((a) >= (b), "<", ">=", a, b);   \
    ASSERT((a) <=  (B), ">", "<=", a, B);  \
 } while (0);                              \
 })

#ifdef __cplusplus
}
#endif

#endif
