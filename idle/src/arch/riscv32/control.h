// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __IDLE_ARCH_RISCV32_CONTROL_H
#define __IDLE_ARCH_RISCV32_CONTROL_H

#ifndef __IDLE_ARCH_CONTROL_H
# error "Should be used directly, use arch/control.h instead"
#endif

// TODO: check value
#define MSTATUS_SPIE (1 << 5)

/**
 * @brief Go to U-mode from M-mode
 *
 * Set mepc to idle entrypoint
 * Enable hardware interrupts in mstatus
 *
 */
static inline __attribute__((naked)) void __switch_to_userspace(
    void (*fn)(unsigned int, unsigned int), unsigned int arg0, unsigned int arg1
)
{
    // asm volatile(
    //     "csrw mepc, %[mepc] \r\t"
    //     "csrw mstatus, %[mstatus]"
    //     :
    //     : [mepc] "r" (fn),
    //       [mstatus] "r" (MSTATUS_SPIE)
    // );

    register unsigned int a0 asm("a0") = arg0;
    register unsigned int a1 asm("a1") = arg1;

    asm volatile("mret" : : "r" (a0), "r" (a1));

    __builtin_unreachable();
}

#endif /* __IDLE_ARCH_RISCV32_CONTROL_H */
