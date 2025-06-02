// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __PLATFORM_H_
#define __PLATFORM_H_

#ifndef PLATFORM_H
#error "arch specific header must not be included directly!"
#endif

#include <limits.h>
#include <sentry/arch/asm-x86_64/thread.h>
#include <sentry/io.h>

#define THREAD_MODE_USER    0xab2f5332UL
#define THREAD_MODE_KERNEL  0x5371a247UL

#ifndef __WORDSIZE
#define __WORDSIZE 4UL
#endif

// __STATIC_INLINE is defined in CMSIS which not standard on RISCV
#ifndef __STATIC_INLINE
#define __STATIC_INLINE static inline
#endif


/**
  \brief   Wait For Interrupt
  \details Wait For Interrupt is a hint instruction that suspends execution until one of a number of events occurs.
 */
#define __WFI()                             asm volatile("wfi")


/**
  \brief   Wait For Event
  \details Wait For Event is a hint instruction that permits the processor to enter
           a low-power state until one of a number of events occurs.
 */
#define __WFE()                             asm volatile("nop")

/**
 * @def alignment size of sections. 8bytes on x86_64
 */
#define SECTION_ALIGNMENT_LEN 0x8UL

static inline void __attribute__((noreturn)) __platform_spawn_thread(size_t entrypoint __attribute__((unused)),
                                                                     stack_frame_t *stack_pointer  __attribute__((unused)),
                                                                     uint32_t flag __attribute__((unused)))
{
  /* TODO: by now, nothing done in x86_64 test mode. Maybe execv() */
  do { } while (1);
}

static inline void __platform_clear_flags(void) {
    return;
}

void __platform_init(void);


#endif/*!__PLATFORM_H_*/
