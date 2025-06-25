// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DRV_RCC_H
#define DRV_RCC_H

#include <inttypes.h>
#include <stdbool.h>

#include <sentry/ktypes.h>

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/buses.h>
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/buses.h>
#else
#error "unsupported architecture!"
#endif

/**
 * @brief RCC options control flags for configuration functions
 *
 * extendable if needed, avoiding any API incompatible upgrade.
 */
typedef enum rcc_opts {
    RCC_NOFLAG = 0,             /**< default, no flags*/
    RCC_LPCONFIG = 0x1UL << 1,  /**< Low power specific configuration */
} rcc_opts_t;


/**
 * @brief Probe and reset the RCC clock configuration
 */
kstatus_t rcc_probe(void);

#if CONFIG_BUILD_TARGET_DEBUG
kstatus_t rcc_enable_debug_clockout(void);
#endif

/**
 * @brief get current core frequency in Hertz
 */
uint32_t rcc_get_core_frequency(void);

kstatus_t rcc_enable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags);

kstatus_t rcc_disable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags);

kstatus_t rcc_get_bus_clock(bus_id_t busid, uint32_t *busclk);

kstatus_t rcc_mux_select_clock_source(uint32_t clk_reg, uint32_t clkmsk, uint32_t val);

#endif/*DRV_RCC_H*/
