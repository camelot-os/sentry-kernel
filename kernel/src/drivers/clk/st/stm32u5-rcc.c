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

#include <sentry/arch/asm-cortex-m/dwt.h>
#include <bsp/drivers/clk/rcc.h>

#include "stm32-rcc.h"
#include "stm32u5-rcc.h"
#include "stm32u5-pll.h"
#include "stm32u5-pwr.h"

static const stm32u5_pll_cfg_t stm32u5_pll1_config = {
    .n = 120, /* VCO out = VCO in * n = 4*120 = 480MHz */
    .frac = 0,
    .m = 4, /* VCO in = HSE/4 ==> 16/4 = 4MHz /*/
    .p = 3,
    .q = 3,
    .r = 3, /* PLL1 R ==> VCO out / R = 480/3 = 160MHz */
};

static const stm32u5_pll_cfg_t stm32u5_pll3_config = {
    .n = 99,
    .frac = 0,
    .m = 4,
    /* XXX:
     *  Might be PLL3 P ==> MIPI DSI byte lane clock @49.5MHz
     * **BUT**
     *  In FW4HW PoC this is configured @66MHz despite byte lane clock computation
     *  This is working this way and this is a strong enough argument for a demo ;-)
     *
     * Must be fixed/consolidated in next milestone(s)
     */
    .p = 6,
    .q = 6,
    .r = 12, /* PLL3 R ==> LTDC @33MHz */
};

#define STM32U5_MUX_REG_RANGE RANGE(RCC_CCIPR1_REG, RCC_CCIPR3_REG)

kstatus_t rcc_mux_select_clock_source(uint32_t clk_reg, uint32_t clkmsk, uint32_t val)
{
    kstatus_t status = K_STATUS_OKAY;
    uint32_t shift;
    uint32_t regval;

    if (unlikely(!IN_RANGE(clk_reg, STM32U5_MUX_REG_RANGE))) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    /*
     * Returns one plus the index of the least significant 1-bit of x,
     * or if x is zero, returns zero.
     */
    shift = __builtin_ffsl(clkmsk);
    if (unlikely(shift == 0)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    regval = ioread32(RCC_BASE_ADDR + clk_reg);
    regval &= ~clkmsk;
    regval |= (val << (shift - 1)) & clkmsk;
    iowrite32(RCC_BASE_ADDR + clk_reg, regval);

err:
    return status;
}

kstatus_t rcc_select_system_clock(void)
{
    uint32_t cfgr1;
    uint32_t count = 0UL;
    /*
     * XXX: For clock delta >= 80MHz
     *  - set HPRE to div by 2
     *  - select PLL as sysclk
     *  - wait at least 5µs
     *  - set HPRE to div by 1
     */

    /* XXX: 0x8 ==> 0b1000 ==> div by 2*/
    __stm32_rcc_set_peripheral_bus_div(0x8, 0, 0, 0);
    cfgr1 = ioread32(RCC_BASE_ADDR + RCC_CFGR1_REG);
    cfgr1 |= RCC_CFGR1_SW_MASK; /* XXX: 0b11 ==> PLL1_R as sysclk */
    iowrite32(RCC_BASE_ADDR + RCC_CFGR1_REG, cfgr1);

    do {
        cfgr1 = ioread32(RCC_BASE_ADDR + RCC_CFGR1_REG) & RCC_CFGR1_SWS_MASK;
        count++;
    } while ((cfgr1 != RCC_CFGR1_SWS_MASK) && (count < PLL_STARTUP_TIMEOUT)); /* XXX: same timeout as PLL ?! */

    /* XXX
     * - here, SYSCLK == 160MHz, HCLK == 80MHz
     *  Count cycle to reach at least 5µs and then bump HCLK to 160MHz
     *  --> wait ~800 cycles
     */
    dwt_reset_cyccnt();
    while(dwt_cyccnt() < (3* 800UL));

    /* configure APB1 freq to sysfreq / 4 (i.e. 40Mhz) */
    __stm32_rcc_set_peripheral_bus_div(0, 5, 0, 0);

    return K_STATUS_OKAY;
}

/*
 * XXX:
 *  hardcoded PLL for Gany demo
 *
 * PLL1 w/ HSE clk source @160MHz
 * PLL3P (mipi) @62.5MHz
 * PLL3R (ltdc) @20.833...MHz
 */
kstatus_t rcc_enable_pll(void)
{

    /*
     * XXX:
     *  Clock config workflow
     *    - PLL1 boost prescaler
     *    - PLL1 boost enable
     *    - Select PLL1 clk source (HSE @16MHz) (already on, must be enabled in dts)
     *    - Set voltage scale (mode 1)
     *    - Enable voltage scale boost
     *    - Configure PLLs
     *    - select clock source (see rcc_select_system_clock)
     */

    stm32u5_pll_epod_booster_prescaler(1);
    stm32u5_pll_select_clock_source(PLL_ID_1, PLL_SRC_CLK_HSE);
    stm32u5_pll_select_clock_source(PLL_ID_3, PLL_SRC_CLK_HSE);
    __stm32u5_pwr_set_voltage_scaling(POWER_VOS_SCALE_1);
    __stm32u5_pwr_enable_epod_boost();

    stm32u5_pll_configure(PLL_ID_1, stm32u5_pll1_config);
    stm32u5_pll_start(PLL_ID_1);
    stm32u5_enable_pll_r_output(PLL_ID_1);

    stm32u5_pll_configure(PLL_ID_3, stm32u5_pll3_config);
    stm32u5_pll_start(PLL_ID_3);
    stm32u5_enable_pll_p_output(PLL_ID_3);
    stm32u5_enable_pll_r_output(PLL_ID_3);

    return K_STATUS_OKAY;
}


#if CONFIG_BUILD_TARGET_DEBUG
kstatus_t rcc_enable_debug_clockout(void)
{
    return K_STATUS_OKAY;
}
#endif /* CONFIG_BUILD_TARGET_DEBUG */
