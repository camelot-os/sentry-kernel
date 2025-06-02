// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <assert.h>

#include <sentry/arch/asm-rv32/systick.h>

#define CLINT_BASE_ADDR 0x02000000 // FIXME: configure base address
#define MTIMECMP_ADDR   CLINT_BASE_ADDR + 0x4000 // Hyp: one core

static uint64_t jiffies;

uint64_t systime_get_jiffies(void)
{
    return jiffies;
}

/**
 * Use CLINT Machine Timer registers
 *
 * Enabling Timer interrupts procedure:
 *  - Enable machine timer interrupts in mie.MTIE
 */
 /*@
  assigns ghost_systick_initialized;
  assigns jiffies;
 */
void systick_init(void)
{
  /*@ assert ghost_systick_initialized == false; */

  jiffies = 0ULL;

  // TODO

  // Enable Machine Timer Interrupts
  // asm volatile (
  //   "lw t0, 0x80 \r\n" // MTIE at offset 7
  //   "csrs mie, t0" // Enable MTIE
  // );

  // Setting the timer
  // asm volatile (
  //   "lw t0, 500000 \r\n" // Arbitrary timer value
  //   "lw t1, %0 \r\n"
  //   "sw t0, 0(t1)" // Set timer comper value
  //     :
  //     : "r" (MTIMECMP_ADDR) // Address of mtimercmp
  // );

  /*@ ghost_systick_initialized = true; */
}

/*@
  assigns jiffies;
 */
stack_frame_t *systick_handler(stack_frame_t * stack_frame)
{
  jiffies++;

  return stack_frame;
}