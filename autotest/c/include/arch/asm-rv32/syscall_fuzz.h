// SPDX-FileCopyrightText: 2026 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

/**
 * \file Raw syscall fuzzing helpers for RV32.
 */
#include <inttypes.h>
#include <types.h>

#ifndef AUTOTEST_ASM_RV32_SYSCALL_FUZZ_H
#define AUTOTEST_ASM_RV32_SYSCALL_FUZZ_H

#ifndef AUTOTEST_SYSCALL_FUZZ_H
#error "must not be included directly, use <syscall_fuzz.h> instead"
#endif

__attribute__((always_inline))
static inline Status __raw_sys_send_ipc_u32(taskh_t target, uint32_t len)
{
    register uint32_t a0 __asm("a0") = (uint32_t)target;
    register uint32_t a1 __asm("a1") = len;
    register uint32_t a7 __asm("a7") = (uint32_t)SYSCALL_SEND_IPC;

    __asm volatile(
        "ecall\n\t"
        : "+r"(a0)
        : "r"(a1), "r"(a7)
        : "memory");

    return (Status)a0;
}

__attribute__((always_inline))
static inline Status __raw_sys_invalid_255(void)
{
    register uint32_t a0 __asm("a0") = 0U;
    register uint32_t a7 __asm("a7") = 255U;

    __asm volatile(
        "ecall\n\t"
        : "+r"(a0)
        : "r"(a7)
        : "memory");

    return (Status)a0;
}

#endif
