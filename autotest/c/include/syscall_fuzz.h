// SPDX-FileCopyrightText: 2026 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

/**
 * \file Raw syscall helpers dedicated to autotest fuzzing.
 */

#ifndef AUTOTEST_SYSCALL_FUZZ_H
#define AUTOTEST_SYSCALL_FUZZ_H

#include <stdint.h>

#include <uapi/types.h>

#if defined(__arm__)
#include <arch/asm-cortex-m/syscall_fuzz.h>
#elif defined(CONFIG_ARCH_RV32)
#include <arch/asm-rv32/syscall_fuzz.h>
#else
#error "unsupported architecture"
#endif

__attribute__((always_inline))
static inline Status raw_sys_send_ipc_u32(taskh_t target, uint32_t len)
{
    return __raw_sys_send_ipc_u32(target, len);
}

__attribute__((always_inline))
static inline Status raw_sys_invalid_255(void)
{
    return __raw_sys_invalid_255();
}

#endif