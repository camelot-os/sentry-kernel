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
#include "stm32u5-rcc.h"

#define STM32U5_PLL_CFGRn_OFFSET 4UL
#define STM32U5_PLL_DIVRn_OFFSET 8UL
#define STM32U5_PLL_FRACn_OFFSET 8UL

/*
 * PLL register are interleaved between PLL1/2/3:
 *  - PLL1CFGR offset  0x28
 *  - PLL2CFGR offset  0x2C
 *  - PLL3CFGR offset  0x30
 *  - PLL1DIVR offset  0x34
 *  - PLL1FRACR offset 0x38
 *  - PLL2DIVR offset  0x3C
 *  - PLL2FRACR offset 0x40
 *  - PLL3DIVR offset  0x44
 *  - PLL3FRACR offset 0x48
 */
#define STM32U5_RCC_PLL_CFGRn_REG(n) (RCC_BASE_ADDR + RCC_PLL1CFGR_REG + ((n) << 2))
#define STM32U5_RCC_PLL_DIVRn_REG(n) (RCC_BASE_ADDR + RCC_PLL1DIVR_REG + ((n) << 3))
#define STM32U5_RCC_PLL_FRACn_REG(n) (RCC_BASE_ADDR + RCC_PLL1FRACR_REG + ((n) << 3))

__STATIC_INLINE void stm32u5_pll_cfgr_write(stm32u5_pll_id_t pll_id, uint32_t value)
{
    iowrite32(STM32U5_RCC_PLL_CFGRn_REG(pll_id), value);
}

__STATIC_INLINE void stm32u5_pll_divr_write(stm32u5_pll_id_t pll_id, uint32_t value)
{
    iowrite32(STM32U5_RCC_PLL_DIVRn_REG(pll_id), value);
}

__STATIC_INLINE void stm32u5_pll_fracr_write(stm32u5_pll_id_t pll_id, uint32_t value)
{
    iowrite32(STM32U5_RCC_PLL_FRACn_REG(pll_id), value);
}

__STATIC_INLINE uint32_t stm32u5_pll_cfgr_read(stm32u5_pll_id_t pll_id)
{
    return ioread32(STM32U5_RCC_PLL_CFGRn_REG(pll_id));
}

__STATIC_INLINE uint32_t stm32u5_pll_divr_read(stm32u5_pll_id_t pll_id)
{
    return ioread32(STM32U5_RCC_PLL_DIVRn_REG(pll_id));
}

__STATIC_INLINE uint32_t stm32u5_pll_fracr_read(stm32u5_pll_id_t pll_id)
{
    return ioread32(STM32U5_RCC_PLL_FRACn_REG(pll_id));
}

/**
 * @brief enable PLLx fractional multiplier
 *
 * @param pll_id PLL id
 *
 * @note Can be change on the fly while PLL is running
 */
__STATIC_INLINE void stm32u5_pll_enable_fractional(stm32u5_pll_id_t pll_id)
{
    uint32_t cfgr = stm32u5_pll_cfgr_read(pll_id);
    cfgr |= RCC_PLL1CFGR_PLL1FRACEN;
    stm32u5_pll_cfgr_write(pll_id, cfgr);
}

/**
 * @brief disable PLLx fractional multiplier
 *
 * @param pll_id PLL id
 *
 * @note Can be change on the fly while PLL is running
 */
__STATIC_INLINE void stm32u5_pll_disable_fractional(stm32u5_pll_id_t pll_id)
{
    uint32_t cfgr = stm32u5_pll_cfgr_read(pll_id);
    cfgr &= ~RCC_PLL1CFGR_PLL1FRACEN;
    stm32u5_pll_cfgr_write(pll_id, cfgr);
}

/**
 * @brief Set EPOD booster prescaler
 *
 * @param pre prescaler, must be in range [1..16], EPOD input clock = (pre >> 1) & 0xf
 *
 * 0000: division by 1 (bypass)
 * 0001: division by 2
 * 0010: division by 4
 * 0011: division by 6
 * 0100: division by 8
 * 0101: division by 10
 * 0110: division by 12
 * 0111: division by 14
 * 1000: division by 16
 *
 * @note EPOD booster clock source is the same as PLL1
 */
void stm32u5_pll_epod_booster_prescaler(uint8_t pre)
{
    uint32_t pll1cfgr = stm32u5_pll_cfgr_read(PLL_ID_1);
    pll1cfgr &= ~RCC_PLL1CFGR_PLL1MBOOST_MASK;
    pll1cfgr |=  ((pre >> 1) << RCC_PLL1CFGR_PLL1MBOOST_SHIFT) & RCC_PLL1CFGR_PLL1MBOOST_MASK;
    stm32u5_pll_cfgr_write(PLL_ID_1, pll1cfgr);
}

/**
 * @brief Select PLLx clock source
 *
 * @param pll pll id
 * @param src pll clock source
 *
 * @return K_ERROR_INVPARAM if pll id or clock source is invalid
 *         K_STATUS_OKAY otherwise
 *
 * @warning PLL must be stopped while changing clock source
 *          Clock source must be ready before use as clock source
 */
kstatus_t stm32u5_pll_select_clock_source(stm32u5_pll_id_t pll, stm32u5_pll_src_clk_t src)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t cfgr;

    if (unlikely((!(pll < PLL_ID_INVALID)) || !(src < PLL_SRC_INVALID))) {
        goto ret;
    }

    cfgr = stm32u5_pll_cfgr_read(pll);
    cfgr &= ~RCC_PLL1CFGR_PLL1SRC_MASK;
    cfgr |= (src << RCC_PLL1CFGR_PLL1SRC_SHIFT) & RCC_PLL1CFGR_PLL1SRC_MASK;
    stm32u5_pll_cfgr_write(pll, cfgr);
    status = K_STATUS_OKAY;

ret:
    return status;
}

kstatus_t stm32u5_pll_set_fractional(stm32u5_pll_id_t pll, uint16_t frac)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(!(pll < PLL_ID_INVALID))) {
        goto ret;
    }

    stm32u5_pll_disable_fractional(pll);
    stm32u5_pll_fracr_write(pll, (frac << RCC_PLL1FRACR_PLL1FRACN_SHIFT) & RCC_PLL1FRACR_PLL1FRACN_MASK);
    stm32u5_pll_enable_fractional(pll);
    status = K_STATUS_OKAY;

ret:
    return status;
}

kstatus_t stm32u5_pll_configure(stm32u5_pll_id_t pll, stm32u5_pll_cfg_t cfg)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t cfgr;
    uint32_t divr;

    if (unlikely(!(pll < PLL_ID_INVALID))) {
        goto ret;
    }

    cfgr = stm32u5_pll_cfgr_read(pll);
    cfgr &= ~RCC_PLL1CFGR_PLL1M_MASK;
    cfgr |= ((cfg.m  - 1) << RCC_PLL1CFGR_PLL1M_SHIFT) & RCC_PLL1CFGR_PLL1M_MASK;
    stm32u5_pll_cfgr_write(pll, cfgr);

    divr = ((cfg.n + 1) << RCC_PLL1DIVR_PLL1N_SHIFT) & RCC_PLL1DIVR_PLL1N_MASK;
    divr |= ((cfg.p - 1) << RCC_PLL1DIVR_PLL1P_SHIFT) & RCC_PLL1DIVR_PLL1P_MASK;
    divr |= ((cfg.q - 1) << RCC_PLL1DIVR_PLL1Q_SHIFT) & RCC_PLL1DIVR_PLL1Q_MASK;
    divr |= ((cfg.r - 1) << RCC_PLL1DIVR_PLL1R_SHIFT) & RCC_PLL1DIVR_PLL1R_MASK;
    stm32u5_pll_divr_write(pll, divr);

    if (cfg.frac > 0) {
        stm32u5_pll_set_fractional(pll, cfg.frac);
    }

    status = K_STATUS_OKAY;

ret:
    return status;
}

kstatus_t stm32u5_pll_start(stm32u5_pll_id_t pll)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t cr;
    uint32_t on_bit;
    uint32_t rdy_bit;

    if (unlikely(!(pll < PLL_ID_INVALID))) {
        goto ret;
    }

    /*
     * ON/RDY bits:
     *  - PLL1 == 24/25
     *  - PLL2 == 26/27
     *  - PLL3 == 28/29
     */
    on_bit = 1 << (RCC_CR_PLL1ON_SHIFT + 2 * pll);
    rdy_bit = 1 << (RCC_CR_PLL1RDY_SHIFT + 2 * pll);

    cr = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
    cr |= on_bit;
    iowrite32(RCC_BASE_ADDR + RCC_CR_REG, cr);

    status = iopoll32_until_set(RCC_BASE_ADDR + RCC_CR_REG, rdy_bit, PLL_STARTUP_TIMEOUT);

ret:
    return status;
}

__STATIC_INLINE kstatus_t stm32u5_enable_pll_output(stm32u5_pll_id_t pll, uint32_t out_en)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t cfgr;

    if (unlikely(!(pll < PLL_ID_INVALID))) {
        goto ret;
    }

    cfgr = stm32u5_pll_cfgr_read(pll);
    cfgr |= out_en;
    stm32u5_pll_cfgr_write(pll, cfgr);
    status = K_STATUS_OKAY;

ret:
    return status;
}

kstatus_t stm32u5_enable_pll_p_output(stm32u5_pll_id_t pll)
{
    return stm32u5_enable_pll_output(pll, RCC_PLL1CFGR_PLL1PEN);
}

kstatus_t stm32u5_enable_pll_q_output(stm32u5_pll_id_t pll)
{
    return stm32u5_enable_pll_output(pll, RCC_PLL1CFGR_PLL1QEN);
}

kstatus_t stm32u5_enable_pll_r_output(stm32u5_pll_id_t pll)
{
    return stm32u5_enable_pll_output(pll, RCC_PLL1CFGR_PLL1REN);
}
