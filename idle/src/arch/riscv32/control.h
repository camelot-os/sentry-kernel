// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __IDLE_ARCH_RISCV32_CONTROL_H
#define __IDLE_ARCH_RISCV32_CONTROL_H

#ifndef __IDLE_ARCH_CONTROL_H
# error "Should not be used directly, use arch/control.h instead"
#endif

/**
 * @brief Do nothing, RISC-V thread starts in U-mode
 */
static inline __attribute__((naked)) void __switch_to_userspace()
{
    return ;
}

#endif /* __IDLE_ARCH_RISCV32_CONTROL_H */
