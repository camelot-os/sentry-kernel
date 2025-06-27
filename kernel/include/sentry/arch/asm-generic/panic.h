// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef PANIC_H
#define PANIC_H

/**
 * \file interrupts controller entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/handler.h>
#elif defined(__x86_64__)
// nothing, userspace mode
#elif defined(__i386__)
// nothing, userspace mode
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/handler.h>
#else
#error "unsupported architecture!"
#endif
#include <sentry/managers/debug.h>


typedef enum panic_event {
    /**< user hard fault: untrappable fault */
    PANIC_USER_HARDFAULT = 0,
    /**< kernel hard fault: utrappable fault */
    PANIC_KERNEL_HARDFAULT,
    /**< user bus fault: fault consequence of invalid bus access transaction */
    PANIC_USER_BUSFAULT,
    /**< kernel hard fault: fault consequence of invalid bus access transaction */
    PANIC_KERNEL_BUSFAULT,
    /**< user usage fault: usage fault such as div by zero and others */
    PANIC_USER_USAGEFAULT,
    /**< kernel usage fault: usage fault such as div by zero and others */
    PANIC_KERNEL_USAGEFAULT,
    /**< memory fault: bad memory access from user */
    PANIC_USER_MEMACCESS,
    /**< memory fault: bad memory access from kernel */
    PANIC_KERNEL_MEMACCESS,
    /**< invalid userspace input that has not been sanitized where it should have */
    PANIC_KERNEL_INVALID_USERSPACE_INPUT,
    /**< kernel buffers too small to handle event: config problem */
    PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG,
    /**< current manager is in invalid state for current event */
    PANIC_KERNEL_INVALID_MANAGER_STATE,
    /**< manager didn't respond as required */
    PANIC_KERNEL_INVALID_MANAGER_RESPONSE,
    /**< kernel has timeouted on a kernel active wait event */
    PANIC_KERNEL_TIMEOUT,
    /**< kernel CFI failed */
    PANIC_KERNEL_BAD_CFI_CALCULATION,
    /**< a hardware IP is in invalid state for/at current event */
    PANIC_HARDWARE_INVALID_STATE,
    /**< a hardware IP has changed while it shouldn't have */
    PANIC_HARDWARE_UNEXPECTED_MODIFICATION,
    /**< a configuration-time mismatch has been detected */
    PANIC_CONFIGURATION_MISMATCH,
    /**< entering an execution flow that should not happen */
    PANIC_UNEXPECTED_BRANCH_EXEC,
    /* max sentinel */
    PANIC_EVENT_MAX,
} panic_event_t;

void panic_print_event(panic_event_t ev);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t panic_emit_signal(panic_event_t ev);
#endif

static inline void
#ifndef CONFIG_BUILD_TARGET_AUTOTEST
__attribute__((noreturn))
#endif
panic(panic_event_t ev) {
#if defined(__arm__) || defined(__FRAMAC__)
    /* calling arch-specific panic handler */
    panic_print_event(ev);
    /* nominal way, do */
    __do_panic();
//# ifdef CONFIG_BUILD_TARGET_AUTOTEST
/** FIXME: may generates recursive uncontrolled call to panic(). To be modified */
//    panic_emit_signal(ev);


#else
    /* ugly warning shutdown for unittest */
    (void)ev;
    /* INFO: clang auto purge protection:
        when a loop with no external impact and with a constant
        loop trigger is implemented, clang just drop it */
    do {
        asm volatile("": : :"memory");
    } while (1);
#endif
}

#endif/*PANIC_H*/
