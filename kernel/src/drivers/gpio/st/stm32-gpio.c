// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32 GPIO controller driver
 */
#include <assert.h>
#include <stdbool.h>
#include <stdatomic.h>

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>
#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/gpio/gpio.h>

#include "gpio_defs.h"
#include "stm32-gpio-dt.h"

static inline kstatus_t gpio_map(uint8_t gpio_port_id)
{
    stm32_gpioport_desc_t const * gpio_desc = stm32_gpioport_get_desc(gpio_port_id);
    return mgr_mm_map_kdev(gpio_desc->base_addr, gpio_desc->size);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t gpio_unmap(void) {
    return mgr_mm_unmap_kdev();
}

kstatus_t gpio_probe(uint8_t gpio_port_id)
{
    kstatus_t status = K_STATUS_OKAY;
    const stm32_gpioport_desc_t* port;

    /*
     * at probe time, we reset the GPIO controler value to their reset state.
     * GPIO A and B have some specific reset values (see RM0090, chap. 8.4.1 and next)
     */
    if (unlikely(gpio_port_id > stm32_get_nr_gpioports())) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    port = stm32_gpioport_get_desc(gpio_port_id);

    /* TODO: handle low power configuration in dts (w/a a dedicatd property) */
    rcc_enable(port->bus_id, port->clk_msk, RCC_NOFLAG);

    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    /**
     * TODO: if GPIO controler is locked, a gpio_unlock(gpio_port_id) is required first
     */
    switch (gpio_port_id) {
        case 0:
            /* GPIO A reset values is specific for a part */
            iowrite32(port->base_addr + GPIO_MODER_REG, 0xa8000000UL);
            iowrite32(port->base_addr + GPIO_OSPEEDR_REG, 0x0c000000UL);
            iowrite32(port->base_addr + GPIO_PUPDR_REG, 0x64000000UL);
            break;
        case 1:
            /* GPIO B reset values is specific for a part */
            iowrite32(port->base_addr + GPIO_MODER_REG, 0x00000280UL);
            iowrite32(port->base_addr + GPIO_OSPEEDR_REG, 0x000000c0UL);
            iowrite32(port->base_addr + GPIO_PUPDR_REG, 0x00000100UL);
            break;
        default:
            /* all others... */
            iowrite32(port->base_addr + GPIO_MODER_REG, 0x0UL);
            iowrite32(port->base_addr + GPIO_OSPEEDR_REG, 0x0UL);
            iowrite32(port->base_addr + GPIO_PUPDR_REG, 0x0UL);
            break;
    }
    /* common reset values for other registers */
    iowrite32(port->base_addr + GPIO_OTYPER_REG, 0x0UL);
    iowrite32(port->base_addr + GPIO_ODR_REG, 0x0UL);
    iowrite32(port->base_addr + GPIO_AFRL_REG, 0x0UL);
    iowrite32(port->base_addr + GPIO_AFRH_REG, 0x0UL);

    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_mode(uint8_t gpio_port_id, uint8_t pin, gpio_mode_t mode)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    size_t reg = ioread32(port_base_addr + GPIO_MODER_REG);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 2) - 1) << (pin*2));
    reg |= (mode << (pin*2));
    iowrite32(port_base_addr + GPIO_MODER_REG, reg);
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_type(uint8_t gpio_port_id, uint8_t pin, gpio_type_t type)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    size_t reg = ioread32(port_base_addr + GPIO_OTYPER_REG);
    reg |= (type << (pin));
    iowrite32(port_base_addr + GPIO_OTYPER_REG, reg);
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_af(uint8_t gpio_port_id, uint8_t pin, gpio_af_t af)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    size_t afreg;
    size_t reg;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }

    if (pin < 8) {
        afreg = port_base_addr + GPIO_AFRL_REG;
    } else {
        afreg = port_base_addr + GPIO_AFRH_REG;
    }
    reg = ioread32(afreg);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 4) - 1) << (pin*4));
    reg |= (af << ((pin % 8)*4));
    iowrite32(afreg, reg);
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_speed(uint8_t gpio_port_id, uint8_t pin, gpio_speed_t speed)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    size_t reg = ioread32(port_base_addr + GPIO_OSPEEDR_REG);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 2) - 1) << (pin*2));
    reg |= (speed << (pin*2));
    iowrite32(port_base_addr + GPIO_OSPEEDR_REG, reg);
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_pull_mode(uint8_t gpio_port_id, uint8_t pin, gpio_pullupd_t pupd)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    size_t reg = ioread32(port_base_addr + GPIO_PUPDR_REG);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 2) - 1) << (pin*2));
    reg |= (pupd << (pin*2));
    iowrite32(port_base_addr + GPIO_PUPDR_REG, reg);
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @ requires \valid(val);
  @*/
kstatus_t gpio_get(uint8_t gpio_port_id, uint8_t pin, bool *val)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
     if (unlikely(val == NULL)) {
        status = K_ERROR_INVPARAM;
     }
     /** FIXME: here, instead of a NULL compatison, a sentry_valid_kernel_data() would
       * be better to start with.
       */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    size_t reg = ioread32(port_base_addr + GPIO_IDR_REG);
    *val = !!(reg & (0x1UL << pin)); /* boolean value normalisation */
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
/**
 * @brief set GPIO ODRx bit to 1
 *
 * Done through BSRR register for atomic 1 shot access
 */
kstatus_t gpio_set(uint8_t gpio_port_id, uint8_t pin)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    iowrite32(port_base_addr + GPIO_BSRR_REG, (0x1ul << (pin)));
    gpio_unmap();
err:
    return status;
}

/*
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
/**
 * @brief reset ODRx bit to 0
 *
 * Done through BSRR register for atomic 1 shot access
 */
kstatus_t gpio_reset(uint8_t gpio_port_id, uint8_t pin)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t port_base_addr = stm32_gpioport_get_desc(gpio_port_id)->base_addr;
    if (unlikely((status = gpio_map(gpio_port_id)) != K_STATUS_OKAY)) {
        goto err;
    }
    iowrite32(port_base_addr + GPIO_BSRR_REG, (0x1ul << (pin+16)));
    gpio_unmap();
err:
    return status;
}
