// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <assert.h>

#include <sentry/arch/asm-rv32/systick.h>
#include <sentry/arch/asm-rv32/riscv-utils.h>

#include <mtimer.h>

/**
 *  NOTE:
 * at library build time, no external dep. This means that these symbols
 * need to be declared by others libraries (required, no weak)
 */
/*@
  // TODO: by do, no border effect as managers not yet proven
  assigns \nothing;
 */
uint64_t systime_get_cycle(void);

/*@
  // TODO: by do, no border effect as managers not yet proven
  assigns \nothing;
 */
stack_frame_t *sched_refresh(stack_frame_t *frame);

/*@
  // TODO: by do, no border effect as managers not yet proven
  assigns \nothing;
 */
void mgr_time_delay_tick(void);

// TODO: for now define an arbitrary timer interval
#define TIMER_INTERVAL 500000

static uint64_t jiffies;

uint64_t systime_get_jiffies(void)
{
    return jiffies;
}

/**
 * @brief Set timecmp
 */
static inline void systick_set_timecmp(uint32_t interval)
{
  asm volatile (
    "li t0, -1 \r\n"
    "sw t0, 0(%0) \r\n"
    "sw %1, 4(%0) \r\n"
    "sw %2, 0(%0)"
    :: "r" (MTIMERCMP_ADDR), "r" (0), "r" (interval)
  );
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

  systick_set_timecmp(TIMER_INTERVAL);

  // Enable Machine Timer Interrupts
  CSR_SET(mie, MIE_TI);

  /*@ ghost_systick_initialized = true; */
}

/*@
  assigns jiffies;
 */
stack_frame_t *systick_handler(stack_frame_t * stack_frame)
{
  jiffies++;

  systime_get_cycle();

#if CONFIG_SCHED_RRMQ
  /* refresh quantums */
  stack_frame = sched_refresh(stack_frame);
#endif

  /* upgrade delayed tasks (sleeping task) */
  mgr_time_delay_tick();

  // Reset timer
  systick_set_timecmp(TIMER_INTERVAL);

  return stack_frame;
}