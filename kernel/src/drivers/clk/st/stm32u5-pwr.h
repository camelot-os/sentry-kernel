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

#ifndef __STM32U5_PWR_H
#define __STM32U5_PWR_H

#include <bsp/drivers/clk/pwr.h>

#define DEFAULT_SCALE_MODE POWER_VOS_SCALE_4

kstatus_t __stm32u5_pwr_set_voltage_scaling(uint8_t scale);
kstatus_t __stm32u5_pwr_enable_epod_boost(void);

#endif /* __STM32U5_PWR_H */
