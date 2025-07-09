// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

/**
 * @file stm32f4xx/stm32l4xx pll driver
 *
 * This is the main pll driver for STM32F4 and STM32L4 family devices.
 * This driver uses registers definition from SVD (ref to peripheral svd generation).
 * Each PLL stage range comes from reference manual in soc dedicated headers.
 * PLL configuration comes from dts file.
 *
 * This driver can configure main PLL:
 *  - VCO input clock source (this clock source is shared w/ SAI PLLs and I2S PLLs if any)
 *  - VCO multiplier/divisor
 *  - VCO P output factor
 *  - VCO Q output factor
 *  - VCO R output factor (stm32l4 only)
 *  - P/Q/R output en/dis-able (stm32l4 only)
 *  - Extra PDIV, on stm32l49x/l4ax only, P output factor is used if PDIV is 0x0000, PDIV otherwise
 *
 * @note this driver need dts node with compatible:
 *  - st,stm32f4xx-pll
 *  - st,stm32l47xx-pll
 *  - st,stm32l49xx-pll
 */

#include <assert.h>

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/buses.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>

#include "rcc_defs.h"
#include "stm32-rcc.h"

#if defined(CONFIG_SOC_SUBFAMILY_STM32L4)
# include "stm32l4-rcc.h"
#elif defined(CONFIG_SOC_SUBFAMILY_STM32F4)
# include "stm32f4-rcc.h"
#else
# error "unsupported SOC"
#endif

#if defined(RCC_PLL_STATUS_OKAY)

static_assert(IN_RANGE(RCC_PLL_VCO_DIVIDER, RCC_PLL_VCO_DIVIDER_RANGE), "VCO divider out of range");
static_assert(IN_RANGE(RCC_PLL_VCO_MULTIPLIER, RCC_PLL_VCO_MULTIPLIER_RANGE), "VCO multiplier out of range");
static_assert(IN_RANGE(RCC_PLL_P_DIVIDER, RCC_PLL_P_DIVIDER_RANGE), "PLL P output divider out of range");
static_assert(IN_RANGE(RCC_PLL_Q_DIVIDER, RCC_PLL_Q_DIVIDER_RANGE), "PLL Q output divider out of range");
static_assert(IN_RANGE(RCC_PLL_VCO_IN_FREQUENCY, RCC_PLL_VCO_INPUT_FREQUENCY_RANGE), "VCO IN frequency invalid, check configuration");
static_assert(IN_RANGE(RCC_PLL_VCO_OUT_FREQUENCY, RCC_PLL_VCO_OUTPUT_FREQUENCY_RANGE), "VCO OUT frequency, check configuration");
static_assert(RCC_PLL_P_OUT_FREQUENCY <= RCC_PLL_P_OUTPUT_FREQUENCY_MAX, "PLL P output frequency out of range");
static_assert(RCC_PLL_Q_OUT_FREQUENCY <= RCC_PLL_Q_OUTPUT_FREQUENCY_MAX, "PLL Q output frequency out of range");


#if defined(CONFIG_SOC_SUBFAMILY_STM32L4)
static_assert((RCC_PLL_Q_DIVIDER % 2) == 0, "Pll Q output divider must be even");
static_assert(IN_RANGE(RCC_PLL_R_DIVIDER, RCC_PLL_R_DIVIDER_RANGE), "Pll R output divider out of range");
static_assert((RCC_PLL_R_DIVIDER % 2) == 0, "Pll R output divider must be even");
static_assert(RCC_PLL_R_OUT_FREQUENCY <= RCC_PLL_R_OUTPUT_FREQUENCY_MAX, "PLL R output frequency out of range");
#elif defined(CONFIG_SOC_SUBFAMILY_STM32F4)
static_assert((RCC_PLL_P_DIVIDER % 2) == 0, "Pll P output divider must be even");
#endif

/**
 * @brief configure stm32f4xx/stm32l4xx main pll
 *
 * @note pllcfg factors and input clock are generated from dts file
 */
__STATIC_INLINE void stm32x4_pll_configure(void)
{
    uint32_t pllcfg = ioread32(RCC_BASE_ADDR + RCC_PLLCFGR_REG);

    /* clear all meaningful bits and let reserved ones at reset value */
    pllcfg &= ~RCC_PLLCFG_CLR_MASK;

    pllcfg |= stm32x4_pllcfg_m_factor();
    pllcfg |= stm32x4_pllcfg_n_factor();
    pllcfg |= stm32x4_pllcfg_p_factor();
    pllcfg |= stm32x4_pllcfg_q_factor();
#if defined(CONFIG_SOC_SUBFAMILY_STM32L4)
    pllcfg |= stm32x4_pllcfg_r_factor();
#endif

    pllcfg |= stm32x4_pllcfg_input();

    iowrite32(RCC_BASE_ADDR + RCC_PLLCFGR_REG, pllcfg);
}

/**
 * @brief Start PLL and wait for PLL to be locked
 *
 * @return K_STATUS_OKAY if pll locked.
 *         K_ERROR_NOTREADY in case of timeout.
 */
__STATIC_INLINE kstatus_t stm32x4_pll_start(void)
{
    uint32_t rcc_cr = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
    rcc_cr |= RCC_CR_PLLON;
    iowrite32(RCC_BASE_ADDR + RCC_CR_REG, rcc_cr);

    return iopoll32_until_set(RCC_BASE_ADDR + RCC_CR_REG, RCC_CR_PLLRDY, PLL_STARTUP_TIMEOUT);
}

/**
 * @brief Enable stm32f4xx/stm32l4xx main pll
 *
 * @note stm32l4xx only: P/Q/R outputs need to be enable independently and after PLL start
 *
 * @return K_STATUS_OKAY in case of success.
 *         K_ERROR_ENOENT if there no such PLL available (i.e. dts node w/ `status=disabled` or no compatible node )
 *         K_ERROR_NOTREADY otherwise.
 */
kstatus_t stm32x4_enable_pll(void)
{
    stm32x4_pll_configure();
    return stm32x4_pll_start();
}

#else /* defined(RCC_PLL_STATUS_OKAY) */
kstatus_t stm32x4_enable_pll(void)
{
    return K_ERROR_NOENT;
}
#endif /* defined(RCC_PLL_STATUS_OKAY) */
