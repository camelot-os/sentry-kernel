// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include "timer_defs.h"
#include "stm32-basic-timer-dt.h"
#include <io.h>
#include <uapi/uapi.h>

/**
 * FIXME: prescaler config depends on timer bus (u5: APB1) clock, in order to
 * deduce the valid prescaling configuration.
 * This request (future PM enhancement) that a userspace driver can get back
 * the current IP input clock frequency to deduce properly the configuration.
 * It is, by now, hard-coded.
 *
 * NOTE: RM0090 (i.e. STM32F4xx) family basic timers can use the very same timer
 * driver implemention as bellow, while the dts is properly set, as the basic timer
 * configuration (without capture support) is the same as basic u5 timers.
 *
 * As a consequence, while using canonical names, there should not need variation
 * in this driver (except prescaling config, see above)
 */

/* hard coded 1s period for autotesting */
int timer_init(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    uint32_t reg = 0;
    uint16_t reg16 = 0;

    /* one pulse mode */
    reg = TIM_CR1_OPM; /* one pulse mode configured */
    iowrite32(desc->base_addr + TIM_CR1_REG, reg);

    /* configure prescaler */
    reg16 = desc->prescaler;
    iowrite16(desc->base_addr + TIM_PSC_REG, reg16);

    /* configure counter */
    reg = desc->counter; /* counter value to 0xffff */
    iowrite32(desc->base_addr + TIM_CNT_REG, reg);

    /* configure auto-relload (no dithering mode) */
    iowrite32(desc->base_addr + TIM_ARR_REG, reg);

    reg = 0;
    /* enable interrupt update */
    reg |= TIM_DIER_UIE;
    iowrite32(desc->base_addr + TIM_DIER_REG, reg);
    __sys_irq_enable(desc->irqn);
    return 0;
}

int timer_enable(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();

    uint32_t reg = ioread32(desc->base_addr + TIM_CR1_REG);
    reg |= TIM_CR1_CEN;
    iowrite32(desc->base_addr + TIM_CR1_REG, reg);
    return 0;
}

int timer_release(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();

    uint32_t reg = 0;
    iowrite32(desc->base_addr + TIM_DIER_REG, reg);
    return 0;
}

int timer_enable_interrupt(void)
{
    uint32_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* enable interrupt update */
    reg |= TIM_DIER_UIE;
    iowrite32(desc->base_addr + TIM_DIER_REG, reg);
    __sys_irq_enable(desc->irqn);
    return 0;
}

uint8_t timer_get_irqn(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();

    return desc->irqn;
}

int timer_set_periodic(void)
{
    int res = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    uint32_t reg;
    /* one pulse mode */
    reg = ioread32(desc->base_addr + TIM_CR1_REG);
    reg &= ~TIM_CR1_OPM;
    iowrite32(desc->base_addr + TIM_CR1_REG, reg);
    return 0;
}


int timer_disable_interrupt(void)
{
    uint32_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* disable interrupt update */
    iowrite32(desc->base_addr + TIM_DIER_REG, reg);
    return 0;
}

int timer_interrupt_acknowledge(void)
{
    uint16_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* clearing interrupt update flag */
    iowrite32(desc->base_addr + TIM_SR_REG, reg);
    return 0;
}

int timer_restart(void)
{
    uint16_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    reg |= TIM_EGR_UG;
    /* clearing interrupt update flag */
    iowrite32(desc->base_addr + TIM_EGR_REG, reg);
    return 0;
}

Status timer_map(devh_t *handle)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    Status res;
    res = __sys_get_device_handle(desc->label);
    if (res != STATUS_OK) {
        goto end;
    }
    copy_from_kernel((uint8_t*)handle, sizeof(devh_t));
    res = __sys_map_dev(*handle);
    if (res != STATUS_OK) {
        goto end;
    }
end:
    return res;
}

Status timer_unmap(devh_t handle)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    Status res;
    res = __sys_unmap_dev(handle);
    if (res != STATUS_OK) {
        goto end;
    }
end:
    return res;
}
