// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef INTERRUPT_H
#define INTERRUPT_H

/**
 * \file interrupts controller entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/nvic.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/apic.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/apic.h>
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/plic.h>
#else
#error "unsupported architecture!"
#endif

#endif/*INTERRUPT_H*/
