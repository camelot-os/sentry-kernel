// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __PLATFORM_H_
#define __PLATFORM_H_

#ifdef __cplusplus
extern "C" {
#endif

#ifndef PLATFORM_H
#error "arch specific header must not be included directly!"
#endif

#include <limits.h>
#include <sentry/io.h>
#include <sentry/arch/asm-rv32/thread.h>
#include <sentry/arch/asm-rv32/plic.h>
#include <sentry/arch/asm-rv32/membarriers.h>
#include <sentry/arch/asm-rv32/riscv-utils.h>

#define THREAD_MODE_USER 0xab2f5332UL
#define THREAD_MODE_KERNEL 0x5371a247UL

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
#define __WFI() asm volatile("wfi")

/**
  \brief   Wait For Event
  \details No real wfe in RISC-V
 */
#define __WFE() asm volatile("nop")

/**
 * @def alignment size of sections. 8bytes on x86_64
 */
#define SECTION_ALIGNMENT_LEN 0x8UL

/**
 * @brief spawn a thread in User mode
 *
 */
static inline void __attribute__((noreturn))
  __platform_spawn_thread(size_t entrypoint __attribute__((unused)),
                            stack_frame_t *stack_pointer __attribute__((unused)),
                            uint32_t flag __attribute__((unused)))
{
  // TODO: Setup new empty stack

  // Set mepc to thread entrypoint
  CSR_WRITE(mepc, entrypoint);

  // Enable interrupts so that thread can be preemptible
  interrupt_enable();

  // Jump to thread
  asm volatile("mret");

  __builtin_unreachable();
}

static inline void __platform_clear_flags(void)
{
  // TODO
  return;
}

void __platform_init(void);

/*@
   // Used at boot time to print out startup SP
   // can be, in Frama-C use case, deactivated (pr_info need only)
   assigns \nothing;
   ensures \result == 0;
 */
static inline uint32_t __platform_get_current_sp(void)
{
  uint32_t sp = 0;
#ifndef __FRAMAC__
  asm volatile("mv %0, sp": "=r" (sp):);
#endif
  return sp;
}

static inline void __platform_enforce_alignment(void)
{
  // TODO
  request_data_membarrier();
}

#ifdef __cplusplus
}
#endif

#endif /*!__PLATFORM_H_*/
