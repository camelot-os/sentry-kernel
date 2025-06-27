// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARCH_GEN_MEMORY_H
#define ARCH_GEN_MEMORY_H

/**
 * \file memory protection entrypoint
 */

#ifdef __cplusplus
extern "C" {
#endif

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/mpu.h>
#include <sentry/arch/asm-cortex-m/handler.h>
#elif defined(__x86_64__)
// TODO add core,mmu and handler headers (or minimum to compile)
#include <sentry/arch/asm-x86_64/memory.h>
#elif defined(__i386__)
// TODO add core,mmu and handler headers (or minimum to compile)
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/pmp.h>
#include <sentry/arch/asm-rv32/handler.h>
#include <sentry/arch/asm-generic/platform.h>
#else
#error "unsupported architecture!"
#endif


#ifdef __cplusplus
}
#endif

#endif/*!#ifndef ARCH_GEN_MEMORY_H*/
