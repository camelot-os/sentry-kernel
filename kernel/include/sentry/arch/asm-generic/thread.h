// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ASM_GEN_THREAD_H
#define ASM_GEN_THREAD_H

#ifdef __cplusplus
extern "C" {
#endif
/**
 * \file interrupts controller entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/thread.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/thread.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/thread.h>
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/thread.h>
#else
#error "unsupported architecture!"
#endif

#ifdef __cplusplus
}
#endif

#endif/*ASM_GEN_THREAD_H*/
