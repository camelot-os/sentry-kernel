// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file membarriers entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/membarriers.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/membarriers.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/membarriers.h>
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/membarriers.h>
#else
#error "unsupported architecture!"
#endif
