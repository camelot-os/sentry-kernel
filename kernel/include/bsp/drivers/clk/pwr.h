// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DRV_PWR_H
#define DRV_PWR_H

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

/*
 * TODO:
 * As those are chip relative, we may define in dts binding
 */
#if defined(CONFIG_SOC_SUBFAMILY_STM32L4) || defined(CONFIG_SOC_SUBFAMILY_STM32F4)
# if defined(CONFIG_ARCH_MCU_STM32F401)
/* XXX: there is no scale mode 1 for stm32f401 chip */
typedef enum clk_vos_scale {
    POWER_VOS_SCALE_3   = 0x1UL,
    POWER_VOS_SCALE_2   = 0x2UL,
} clk_vos_scale_t;
/*@
    predicate scale_is_valid(uint8_t s) =
      s == POWER_VOS_SCALE_3 ||
      s == POWER_VOS_SCALE_2;
*/
# elif defined(CONFIG_ARCH_MCU_STM32F439) || defined(CONFIG_ARCH_MCU_STM32F429)
/* Two-bits encoded value on STM32F4(2|3)x */
typedef enum clk_vos_scale {
    POWER_VOS_SCALE_3   = 0x1UL,
    POWER_VOS_SCALE_2   = 0x2UL,
    POWER_VOS_SCALE_1   = 0x3UL,
} clk_vos_scale_t;
/*@
    predicate scale_is_valid(uint8_t s) =
      s == POWER_VOS_SCALE_3 ||
      s == POWER_VOS_SCALE_2 ||
      s == POWER_VOS_SCALE_1;
*/
# else
/* One-bit encoded value on STM32F4(0|1)x */
typedef enum clk_vos_scale {
    POWER_VOS_SCALE_2   = 0x0UL,
    POWER_VOS_SCALE_1   = 0x1UL,
} clk_vos_scale_t;
/*@
    predicate scale_is_valid(uint8_t s) =
      s == POWER_VOS_SCALE_2 ||
      s == POWER_VOS_SCALE_1;
*/
# endif
#elif defined(CONFIG_SOC_SUBFAMILY_STM32U5)
typedef enum clk_vos_scale {
    POWER_VOS_SCALE_4   = 0x0UL,
    POWER_VOS_SCALE_3   = 0x1UL,
    POWER_VOS_SCALE_2   = 0x2UL,
    POWER_VOS_SCALE_1   = 0x3UL,
} clk_vos_scale_t;
/*@
    predicate scale_is_valid(uint8_t s) =
      s == POWER_VOS_SCALE_4 ||
      s == POWER_VOS_SCALE_3 ||
      s == POWER_VOS_SCALE_2 ||
      s == POWER_VOS_SCALE_1;
*/
#elif defined(CONFIG_SOC_SUBFAMILY_STM32WB)
typedef enum clk_vos_scale {
    POWER_VOS_SCALE_1   = 0x1UL,
    POWER_VOS_SCALE_2   = 0x2UL,
} clk_vos_scale_t;
/*@
    predicate scale_is_valid(uint8_t s) =
      s == POWER_VOS_SCALE_2 ||
      s == POWER_VOS_SCALE_1;
*/
#endif
kstatus_t pwr_probe(void);

kstatus_t pwr_set_voltage_regulator_scaling(uint8_t scale);

#endif/*DRV_PWR_H*/
