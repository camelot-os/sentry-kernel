// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>

#if defined(__arm__)
/* need DWT backend for cycle count */
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/dwt.h>
#endif
#include <bsp/drivers/clk/rcc.h>

static uint32_t perfo_cycle_per_usec;

/**
 * @brief Initialize the number of cpu cycle per micro seconds
 *
 * called by clock manager init step, at very early init.
 * This function is not exported out of the manager itself.
 */
kstatus_t perfo_init(void)
{
    uint64_t cycle_per_sec = rcc_get_core_frequency();
    uint64_t tmp = cycle_per_sec / USEC_PER_SEC;

    perfo_cycle_per_usec = (uint32_t)(tmp & 0xffffffffUL);

#if defined(__arm__) || defined(__FRAMAC__)
    /* start carry (number of dwt loops) at 0, to support complete cycle
     * count with 64bit length, supporting, with 168Mhz core, upto ~3300 years of counting
     */
    dwt_enable_cyccnt();
#endif
    /* in x86_64, rdtsc instruction can be used */
    return K_STATUS_OKAY;
}

uint32_t mgr_clock_get_cycle_per_usec(void)
{
    return perfo_cycle_per_usec;
}

/**
 * @brief return current cycle since bootup, allows to be used
 * for stricly unique identifier, or to order precisely timestamps
 */
uint64_t mgr_clock_get_cycle(void)
{
    uint64_t cycles;
#if defined(__arm__) || defined(__FRAMAC__)
    cycles = dwt_cyccnt();
#elif defined(__x86_64__) || defined (__i386__)
    uint32_t lo, hi;
    asm( "rdtsc" : "=a" (lo), "=d" (hi) );
    cycles = (lo | (hi << 32));
#elif defined(CONFIG_ARCH_RV32)
    asm volatile("rdcycle %0" : "=r"(cycles));
#else
# error "unsupported arch"
#endif
    return cycles;
}
