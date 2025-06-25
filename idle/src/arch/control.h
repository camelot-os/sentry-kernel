// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __IDLE_ARCH_CONTROL_H
#define __IDLE_ARCH_CONTROL_H

#if defined(CONFIG_ARCH_ARM_CORTEX_M)
# include "asm-cortex-m/control.h"
#elif defined(CONFIG_ARCH_RV32)
# include "riscv32/control.h"
#else
# error "target arch not supported"
#endif

#endif /* __IDLE_ARCH_CORTEX_M_CONTROL_H */
