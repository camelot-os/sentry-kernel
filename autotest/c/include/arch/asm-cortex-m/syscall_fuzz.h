// SPDX-FileCopyrightText: 2026 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

/**
 * \file Raw syscall fuzzing helpers for ARM Cortex-M.
 */
#include <inttypes.h>
#include <uapi/types.h>

#ifndef AUTOTEST_ASM_CORTEX_M_SYSCALL_FUZZ_H
#define AUTOTEST_ASM_CORTEX_M_SYSCALL_FUZZ_H

#ifndef AUTOTEST_SYSCALL_FUZZ_H
#error "must not be included directly, use <syscall_fuzz.h> instead"
#endif

_Static_assert(SYSCALL_SEND_IPC == 11U, "syscall id mismatch");

__attribute__((always_inline))
static inline Status __raw_sys_send_ipc_u32(taskh_t target, uint32_t len)
{
    register uint32_t r0 __asm("r0") = (uint32_t)target;
    register uint32_t r1 __asm("r1") = len;

    __asm volatile(
        "svc #11\n\t"
        : "+r"(r0)
        : "r"(r1)
        : "memory");

    return (Status)r0;
}

__attribute__((always_inline))
static inline Status __raw_sys_invalid_255(void)
{
    register uint32_t r0 __asm("r0") = 0U;

    __asm volatile(
        "svc #255\n\t"
        : "+r"(r0)
        :
        : "memory");

    return (Status)r0;
}

#endif
