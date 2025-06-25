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
#include <bsp/drivers/clk/pwr.h>

#include "stm32u5-pwr.h"
#include "pwr_defs.h"

#define STM32U5_PWR_TIMEOUT 500UL

__STATIC_INLINE kstatus_t __stm32u5_pwr_wait_vos_ready(void)
{
    return iopoll32_until_set(PWR_BASE_ADDR + PWR_VOSR_REG, PWR_VOSR_VOSRDY, STM32U5_PWR_TIMEOUT);
}

__STATIC_INLINE kstatus_t __stm32u5_pwr_wait_epod_boost_ready(void)
{
    return iopoll32_until_set(PWR_BASE_ADDR + PWR_VOSR_REG, PWR_VOSR_BOOSTRDY, STM32U5_PWR_TIMEOUT);
}

/*@
    requires scale_is_valid(scale);
    assigns *(uint32_t*)(PWR_BASE_ADDR + PWR_VOSR_REG);
    ensures \result == K_STATUS_OKAY;
 */
kstatus_t __stm32u5_pwr_set_voltage_scaling(uint8_t scale)
{
    uint32_t vosr;

    /*@ assert pwr_register_exists(PWR_VOSR_REG); */
    /*@ assert pwr_is_readable_register(PWR_VOSR_REG); */
    vosr = ioread32(PWR_BASE_ADDR + PWR_VOSR_REG);
    vosr &= ~PWR_VOSR_VOS_MASK;
    vosr |= ((scale << PWR_VOSR_VOS_SHIFT) & PWR_VOSR_VOS_MASK);
    /*@ assert pwr_is_writable_register(PWR_VOSR_REG); */
    iowrite32(PWR_BASE_ADDR + PWR_VOSR_REG, vosr);

    return __stm32u5_pwr_wait_vos_ready();
}

kstatus_t __stm32u5_pwr_enable_epod_boost(void)
{
    uint32_t vosr;

    /*@ assert pwr_register_exists(PWR_VOSR_REG); */
    /*@ assert pwr_is_readable_register(PWR_VOSR_REG); */
    vosr = ioread32(PWR_BASE_ADDR + PWR_VOSR_REG);
    vosr |= PWR_VOSR_BOOSTEN;
    /*@ assert pwr_is_writable_register(PWR_VOSR_REG); */
    iowrite32(PWR_BASE_ADDR + PWR_VOSR_REG, vosr);

    return __stm32u5_pwr_wait_epod_boost_ready();
}

kstatus_t pwr_set_voltage_regulator_scaling(uint8_t scale)
__attribute__ ((alias("__stm32u5_pwr_set_voltage_scaling")));
