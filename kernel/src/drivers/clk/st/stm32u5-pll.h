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

#ifndef __STM32U5_PLL_H
#define __STM32U5_PLL_H

#include <sentry/ktypes.h>

#include "stm32u5-rcc.h"

void stm32u5_pll_epod_booster_prescaler(uint8_t pre);
kstatus_t stm32u5_pll_select_clock_source(stm32u5_pll_id_t pll, stm32u5_pll_src_clk_t src);
kstatus_t stm32u5_pll_set_fractional(stm32u5_pll_id_t pll, uint16_t frac);
kstatus_t stm32u5_pll_configure(stm32u5_pll_id_t pll, stm32u5_pll_cfg_t cfg);
kstatus_t stm32u5_pll_start(stm32u5_pll_id_t pll);

kstatus_t stm32u5_enable_pll_p_output(stm32u5_pll_id_t pll);
kstatus_t stm32u5_enable_pll_q_output(stm32u5_pll_id_t pll);
kstatus_t stm32u5_enable_pll_r_output(stm32u5_pll_id_t pll);

#endif /* __STM32U5_PLL_H */
