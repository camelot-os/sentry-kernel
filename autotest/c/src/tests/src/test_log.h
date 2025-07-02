// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef LIBTEST_LOG_H
#define LIBTEST_LOG_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>
#include <uapi/uapi.h>

/**
 * @file log.h
 *
 * testlib logging backend for assert and other testlib frontents.
 */

/** @def USER_AUTOTEST default prefix for all logs */
#define USER_AUTOTEST         "[AT]"
/** @def USER_AUTOTEST_INFO prefix for info logs, to complete informational content */
#define USER_AUTOTEST_INFO    "[INFO      ]"
/** @def USER_AUTOTEST_EXEC prefix for execution message logs */
#define USER_AUTOTEST_EXEC    "[EXE       ]"
/** @def USER_AUTOTEST_START prefix for test start marker */
#define USER_AUTOTEST_START   "[START     ]"
/** @def USER_AUTOTEST_END prefix for test termination marker */
#define USER_AUTOTEST_END     "[END       ]"
/** @def USER_AUTOTEST_FAIL prefix for failing checks such as invalid assertion */
#define USER_AUTOTEST_FAIL    "[KO        ]"
/** @def USER_AUTOTEST_SUCCESS prefix for successful checks such as valid assertion */
#define USER_AUTOTEST_SUCCESS "[SUCCESS   ]"
/** @def USER_AUTOTEST_START_SUITE prefix for test suite start messages */
#define USER_AUTOTEST_START_SUITE   "[STARTSUITE]"
/** @def USER_AUTOTEST_START_SUITE prefix for test suite end messages */
#define USER_AUTOTEST_END_SUITE     "[ENDSUITE  ]"

/**
 * @def backing autotest formatting mechanims, adding function name and line
 *
 * Must not be called directly.
 */
#define pr_autotest_fmt(func, line, fmt) "%s:%d: " fmt "\n", func, line

/**
 * @def autotest messages header macro, that forge the complete line
 *
 * Must not be called directly
 */
#define pr_autotest(type, func, line, fmt, ...) \
	printf(USER_AUTOTEST type " " pr_autotest_fmt(func, line, fmt), ##__VA_ARGS__)

/** @def TEST_START() test starting informational, using current function name and line */
#define TEST_START() do { \
    pr_autotest(USER_AUTOTEST_START, __func__, __LINE__, ""); \
} while (0)

/** @def TEST_START() test termination informational, using current function name and line */
#define TEST_END() do { \
    pr_autotest(USER_AUTOTEST_END, __func__, __LINE__, ""); \
} while (0)

/** @def TEST_SUITE_START() test suite start informational, using current function name and line */
#define TEST_SUITE_START(suitename) do { \
    pr_autotest(USER_AUTOTEST_START_SUITE, __func__, __LINE__, suitename); \
} while (0)

/** @def TEST_SUITE_END() test suite termination informational, using current function name and line */
#define TEST_SUITE_END(suitename) do { \
    pr_autotest(USER_AUTOTEST_END_SUITE, __func__, __LINE__, suitename); \
} while (0)

/** @def LOG() generic informational message. support printf() format */
#define LOG(fmt, ...) \
    printf(USER_AUTOTEST USER_AUTOTEST_INFO " " pr_autotest_fmt(__func__, __LINE__, fmt), ##__VA_ARGS__)


/** @fn failure_u32 failure message format for uint32_t typed argument */
static inline void failure_u32(const char *func, int line, const char*failure, uint32_t a, uint32_t b) {
    pr_autotest(USER_AUTOTEST_FAIL, func, line, "%lu %s %lu", a, failure, b);
}

/** @fn success_u32 success message format for uint32_t typed argument */
static inline void success_u32(const char *func, int line, const char*success, uint32_t a, uint32_t b) {
    pr_autotest(USER_AUTOTEST_SUCCESS, func, line, "%lu %s %lu", a, success, b);
}

/** @fn failure_u64 failure message format for uint64_t typed argument */
static inline void failure_u64(const char *func, int line, const char*failure, uint64_t a, uint64_t b) {
    pr_autotest(USER_AUTOTEST_FAIL, func, line, "%llu %s %llu", a, failure, b);
}

/** @fn success_u64 success message format for uint32_t typed argument */
static inline void success_u64(const char *func, int line, const char*success, uint64_t a, uint64_t b) {
    pr_autotest(USER_AUTOTEST_SUCCESS, func, line, "%llu %s %llu", a, success, b);
}

/** @fn failure_int failure message format for int typed argument */
static inline void failure_int(const char *func, int line, const char*failure, int a, int b) {
    pr_autotest(USER_AUTOTEST_FAIL, func, line, "%d %s %d", a, failure, b);
}

/** @fn success_int failure message format for int typed argument */
static inline void success_int(const char *func, int line, const char*success, int a, int b) {
    pr_autotest(USER_AUTOTEST_SUCCESS, func, line, "%d %s %d", a, success, b);
}

/** @fn success generic API for multi-typed arguments */
#define success(f, l, msg, T,U) _Generic((T),   \
    uint32_t: _Generic((U),                     \
        uint32_t: success_u32,                  \
        int: success_u32,                       \
        uint64_t: success_u64,                  \
        Status: success_u32                     \
    )(f,l,msg,T,U),                             \
    uint64_t: _Generic((U),                     \
        uint32_t: success_u64,                  \
        uint64_t: success_u64,                  \
        Status: success_u64,                    \
        int: success_u64                        \
    )(f,l,msg,T,U),                             \
    int: _Generic((U),                          \
        int: success_int,                       \
        uint32_t: failure_u64,                  \
        uint64_t: failure_u64,                  \
        Status: success_int                     \
    )(f,l,msg,T,U),                             \
    Status: _Generic((U),                       \
        uint32_t: success_u32,                  \
        uint64_t: success_u64,                  \
        int: success_u32,                       \
        Status: success_u32                     \
    )(f,l,msg,T,U)                              \
)

/** @fn failure generic API for multi-typed arguments */
#define failure(f, l, msg, T,U) _Generic((T),   \
    uint32_t: _Generic((U),                     \
        uint32_t: failure_u32,                  \
        uint64_t: failure_u64,                  \
        Status: failure_u32,                    \
        int: success_u32                        \
    )(f,l,msg,T,U),                             \
    uint64_t: _Generic((U),                     \
        uint32_t: failure_u64,                  \
        uint64_t: failure_u64,                  \
        Status: failure_u64,                    \
        int: success_u64                        \
    )(f,l,msg,T,U),                             \
    int: _Generic((U),                          \
        uint32_t: failure_u32,                  \
        uint64_t: failure_u64,                  \
        int: success_int,                       \
        Status: success_int                     \
    )(f,l,msg,T,U),                             \
    Status: _Generic((U),                       \
        uint32_t: failure_u32,                  \
        uint64_t: failure_u64,                  \
        int: success_u32,                       \
        Status: failure_u32                     \
    )(f,l,msg,T,U)                              \
)

#ifdef __cplusplus
}
#endif

#endif
