// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __IDLE_ARCH_CORTEX_M_CONTROL_H
#define __IDLE_ARCH_CORTEX_M_CONTROL_H

#ifndef __IDLE_ARCH_CONTROL_H
# error "Should be used directly, use arch/control.h instead"
#endif

/**
 * @brief Drop privilege and run as unprivileged thread
 *
 * This asm set the nPRIV bit in CONTROL register after idle start-up.
 */
static inline void __switch_to_userspace(
    void (*fn)(unsigned int, unsigned int), unsigned int arg0, unsigned int arg1
)
{
    asm volatile(
        "mrs r0,control \r\n"
        "orr r0,r0,#1 \r\n"
        "msr control, r0 \r\n"
        "isb"
        ::: "memory"
    );

    fn(arg0, arg1);
}

#endif /* __IDLE_ARCH_CORTEX_M_CONTROL_H */
