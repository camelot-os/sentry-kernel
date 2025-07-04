// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
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
#include <bsp/drivers/clk/rcc.h>
#include "pwr_defs.h"

/* TODO: move stm32l4/f4 in a dedicated file */
#if defined(CONFIG_SOC_SUBFAMILY_STM32L4) || defined(CONFIG_SOC_SUBFAMILY_STM32WB)
#define PWR_CR_REG PWR_CR1_REG
#define PWR_CR_VOS_MASK PWR_CR1_VOS_MASK
#define PWR_CR_VOS_SHIFT PWR_CR1_VOS_SHIFT
#elif defined(CONFIG_SOC_SUBFAMILY_STM32U5)
#include "stm32u5-pwr.h"
#endif

/* FIXME */
#if defined(CONFIG_SOC_SUBFAMILY_STM32L4) || defined(CONFIG_SOC_SUBFAMILY_STM32F4) || defined(CONFIG_SOC_SUBFAMILY_STM32WB)
# if defined(CONFIG_ARCH_MCU_STM32F401)
#  define DEFAULT_SCALE_MODE POWER_VOS_SCALE_2
# else
#  define DEFAULT_SCALE_MODE POWER_VOS_SCALE_1
# endif
#endif

/*@
    ensures \result == K_STATUS_OKAY;
  */
kstatus_t pwr_probe(void)
{
    /*
     * This bit controls the main internal voltage regulator output
     * voltage to achieve a trade-off between performance and power
     * consumption when the device does not operate at the maximum
     * frequency. (DocID018909 Rev 15 - page 141)
     * PWR_CR_VOS = 1 => Scale 1 mode (default value at reset)
     */

#if defined(CONFIG_SOC_SUBFAMILY_STM32U5)
    /*
     * FIXME:
     *  Must be set through DTS but there is no PWR node in stm32u5 dtsi.
     */
    rcc_enable(BUS_AHB3, 0x4, 0);
#endif
    return pwr_set_voltage_regulator_scaling(DEFAULT_SCALE_MODE);
}

#if defined(CONFIG_SOC_SUBFAMILY_STM32L4) || defined(CONFIG_SOC_SUBFAMILY_STM32F4) || defined(CONFIG_SOC_SUBFAMILY_STM32WB)
/*@
    requires scale_is_valid(scale);
    ensures \result == K_STATUS_OKAY;
  */
kstatus_t pwr_set_voltage_regulator_scaling(uint8_t scale)
{
    kstatus_t status;
    size_t reg;
    /*@ assert pwr_register_exists(PWR_CR_REG); */
    /*@ assert pwr_is_readable_register(PWR_CR_REG); */
    reg = ioread32(PWR_BASE_ADDR + PWR_CR_REG);
    reg &= ~PWR_CR_VOS_MASK;
    reg |= ((scale << PWR_CR_VOS_SHIFT) & PWR_CR_VOS_MASK);
    /*@ assert pwr_is_writable_register(PWR_CR_REG); */
    iowrite32(PWR_BASE_ADDR + PWR_CR_REG, reg);
    status = K_STATUS_OKAY;
    return status;
}
#endif
