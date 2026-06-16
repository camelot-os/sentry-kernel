// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdatomic.h>

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/gpio/gpio.h>

#include <dt-bindings/reset/rp2350_reset.h>

#if defined(CONFIG_SOC_SUBFAMILY_RP2350)
#include <sentry/arch/asm-cortex-m/buses.h>
#endif
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/io.h>
#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>

#ifndef BUSES_H
typedef enum bus_identifier {
    BUS_GENERIC = 0,
} bus_id_t;

#define BUS_IS_VALID(bus) (true)
#endif

#define RP2350_GPIO_PORT_ID            0u
#define RP2350_GPIO_PIN_COUNT          30u

#define RP2350_IO_BANK0_MAP_SIZE       0x320u
#define RP2350_PADS_BANK0_MAP_SIZE     0xccu
#define RP2350_SIO_MAP_SIZE            0x50u

#define RP2350_IO_BANK0_PIN_STRIDE     0x8u
#define RP2350_IO_BANK0_GPIO_CTRL(pin) (0x4u + ((uint32_t)(pin) * RP2350_IO_BANK0_PIN_STRIDE))

#define RP2350_PADS_BANK0_GPIO(pin)    (0x4u + ((uint32_t)(pin) * 0x4u))

#define RP2350_SIO_GPIO_IN_REG         0x4u
#define RP2350_SIO_GPIO_OUT_REG        0x10u
#define RP2350_SIO_GPIO_OUT_SET_REG    0x18u
#define RP2350_SIO_GPIO_OUT_CLR_REG    0x20u
#define RP2350_SIO_GPIO_OE_SET_REG     0x38u
#define RP2350_SIO_GPIO_OE_CLR_REG     0x40u

#define RP2350_GPIO_CTRL_FUNCSEL_POS   0u
#define RP2350_GPIO_CTRL_FUNCSEL_MSK   (0x1fu << RP2350_GPIO_CTRL_FUNCSEL_POS)

#define RP2350_GPIO_FUNCSEL_SIO        5u
#define RP2350_GPIO_FUNCSEL_NULL       31u
#define RP2350_GPIO_FUNCSEL_MAX        10u

#define RP2350_PADS_GPIO_ISO           (1u << 8)
#define RP2350_PADS_GPIO_OD            (1u << 7)
#define RP2350_PADS_GPIO_IE            (1u << 6)
#define RP2350_PADS_GPIO_DRIVE_POS     4u
#define RP2350_PADS_GPIO_DRIVE_MSK     (0x3u << RP2350_PADS_GPIO_DRIVE_POS)
#define RP2350_PADS_GPIO_PUE           (1u << 3)
#define RP2350_PADS_GPIO_PDE           (1u << 2)
#define RP2350_PADS_GPIO_SCHMITT       (1u << 1)
#define RP2350_PADS_GPIO_SLEWFAST      (1u << 0)

static atomic_uint_fast32_t rp2350_open_drain_mask = 0u;

static inline uint32_t rp2350_gpio_pin_mask(uint8_t pin)
{
    return (1u << pin);
}

static inline kstatus_t rp2350_gpio_validate(uint8_t gpio_port_id, uint8_t pin)
{
    if (unlikely((gpio_port_id != RP2350_GPIO_PORT_ID) || (pin >= RP2350_GPIO_PIN_COUNT))) {
        return K_ERROR_INVPARAM;
    }

    return K_STATUS_OKAY;
}

static inline bool rp2350_gpio_is_open_drain(uint8_t pin)
{
    return ((atomic_load(&rp2350_open_drain_mask) & rp2350_gpio_pin_mask(pin)) != 0u);
}

static kstatus_t rp2350_gpio_map(size_t base_addr, size_t size)
{
    return mgr_mm_map_kdev(base_addr, size);
}

static inline kstatus_t rp2350_gpio_unmap(void)
{
    return mgr_mm_unmap_kdev();
}

static kstatus_t rp2350_gpio_update_ctrl(uint8_t pin, uint32_t clear_mask, uint32_t set_mask)
{
    kstatus_t status;
    uint32_t reg;

    status = rp2350_gpio_map(IO_BANK0_BASE_ADDR, RP2350_IO_BANK0_MAP_SIZE);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    reg = ioread32(IO_BANK0_BASE_ADDR + RP2350_IO_BANK0_GPIO_CTRL(pin));
    reg &= ~clear_mask;
    reg |= set_mask;
    iowrite32(IO_BANK0_BASE_ADDR + RP2350_IO_BANK0_GPIO_CTRL(pin), reg);

    rp2350_gpio_unmap();
    return K_STATUS_OKAY;
}

static kstatus_t rp2350_gpio_update_pad(uint8_t pin, uint32_t clear_mask, uint32_t set_mask)
{
    kstatus_t status;
    uint32_t reg;

    status = rp2350_gpio_map(PADS_BANK0_BASE_ADDR, RP2350_PADS_BANK0_MAP_SIZE);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    reg = ioread32(PADS_BANK0_BASE_ADDR + RP2350_PADS_BANK0_GPIO(pin));
    reg &= ~clear_mask;
    reg |= set_mask;
    iowrite32(PADS_BANK0_BASE_ADDR + RP2350_PADS_BANK0_GPIO(pin), reg);

    rp2350_gpio_unmap();
    return K_STATUS_OKAY;
}

static kstatus_t rp2350_gpio_write_sio(uint32_t reg, uint32_t val)
{
    kstatus_t status;

    status = rp2350_gpio_map(SIO_BASE_ADDR, RP2350_SIO_MAP_SIZE);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    iowrite32(SIO_BASE_ADDR + reg, val);
    rp2350_gpio_unmap();

    return K_STATUS_OKAY;
}

static kstatus_t rp2350_gpio_read_sio(uint32_t reg, uint32_t *val)
{
    kstatus_t status;

    if (unlikely(val == NULL)) {
        return K_ERROR_INVPARAM;
    }

    status = rp2350_gpio_map(SIO_BASE_ADDR, RP2350_SIO_MAP_SIZE);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    *val = ioread32(SIO_BASE_ADDR + reg);
    rp2350_gpio_unmap();

    return K_STATUS_OKAY;
}

static kstatus_t rp2350_gpio_sync_sio_output(uint8_t pin)
{
    kstatus_t status;
    uint32_t output_latch;
    uint32_t pin_mask = rp2350_gpio_pin_mask(pin);

    status = rp2350_gpio_read_sio(RP2350_SIO_GPIO_OUT_REG, &output_latch);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    if (rp2350_gpio_is_open_drain(pin)) {
        if ((output_latch & pin_mask) != 0u) {
            return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_CLR_REG, pin_mask);
        }
        return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_SET_REG, pin_mask);
    }

    return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_SET_REG, pin_mask);
}

kstatus_t gpio_probe(uint8_t gpio_port_id)
{
    kstatus_t status;

    status = rp2350_gpio_validate(gpio_port_id, 0u);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    status = rcc_enable(BUS_GENERIC, RPI_PICO_RESETS_RESET_IO_BANK0, RCC_NOFLAG);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    status = rcc_enable(BUS_GENERIC, RPI_PICO_RESETS_RESET_PADS_BANK0, RCC_NOFLAG);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    atomic_store(&rp2350_open_drain_mask, 0u);
    return K_STATUS_OKAY;
}

kstatus_t gpio_set_mode(uint8_t gpio_port_id, uint8_t pin, gpio_mode_t mode)
{
    kstatus_t status;
    uint32_t pad_clear_mask = RP2350_PADS_GPIO_ISO | RP2350_PADS_GPIO_IE;
    uint32_t pad_set_mask = RP2350_PADS_GPIO_SCHMITT;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    switch (mode) {
        case GPIOx_MODE_INPUT:
            status = rp2350_gpio_update_ctrl(pin, RP2350_GPIO_CTRL_FUNCSEL_MSK,
                                             (RP2350_GPIO_FUNCSEL_SIO << RP2350_GPIO_CTRL_FUNCSEL_POS));
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            status = rp2350_gpio_update_pad(pin, pad_clear_mask, pad_set_mask | RP2350_PADS_GPIO_IE);
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_CLR_REG, rp2350_gpio_pin_mask(pin));

        case GPIOx_MODE_OUT:
            status = rp2350_gpio_update_ctrl(pin, RP2350_GPIO_CTRL_FUNCSEL_MSK,
                                             (RP2350_GPIO_FUNCSEL_SIO << RP2350_GPIO_CTRL_FUNCSEL_POS));
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            status = rp2350_gpio_update_pad(pin, pad_clear_mask, pad_set_mask | RP2350_PADS_GPIO_IE);
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            if (rp2350_gpio_is_open_drain(pin)) {
                status = rp2350_gpio_write_sio(RP2350_SIO_GPIO_OUT_SET_REG, rp2350_gpio_pin_mask(pin));
                if (unlikely(status != K_STATUS_OKAY)) {
                    return status;
                }
            }

            return rp2350_gpio_sync_sio_output(pin);

        case GPIOx_MODE_AF:
            status = rp2350_gpio_update_pad(pin, pad_clear_mask, pad_set_mask | RP2350_PADS_GPIO_IE);
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_CLR_REG, rp2350_gpio_pin_mask(pin));

        case GPIOx_MODE_ANALOG:
            status = rp2350_gpio_update_ctrl(pin, RP2350_GPIO_CTRL_FUNCSEL_MSK,
                                             (RP2350_GPIO_FUNCSEL_NULL << RP2350_GPIO_CTRL_FUNCSEL_POS));
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            status = rp2350_gpio_update_pad(pin,
                                            RP2350_PADS_GPIO_ISO | RP2350_PADS_GPIO_IE | RP2350_PADS_GPIO_SCHMITT,
                                            0u);
            if (unlikely(status != K_STATUS_OKAY)) {
                return status;
            }

            return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_CLR_REG, rp2350_gpio_pin_mask(pin));

        default:
            return K_ERROR_INVPARAM;
    }
}

kstatus_t gpio_set_pull_mode(uint8_t gpio_port_id, uint8_t pin, gpio_pullupd_t pupd)
{
    kstatus_t status;
    uint32_t set_mask = 0u;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    switch (pupd) {
        case GPIOx_NOPULL:
            break;
        case GPIOx_PULLUP:
            set_mask = RP2350_PADS_GPIO_PUE;
            break;
        case GPIOx_PULLDOWN:
            set_mask = RP2350_PADS_GPIO_PDE;
            break;
        default:
            return K_ERROR_INVPARAM;
    }

    return rp2350_gpio_update_pad(pin, RP2350_PADS_GPIO_PUE | RP2350_PADS_GPIO_PDE, set_mask);
}

kstatus_t gpio_set_type(uint8_t gpio_port_id, uint8_t pin, gpio_type_t type)
{
    kstatus_t status;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    switch (type) {
        case GPIOx_TYPE_PPULL:
            atomic_fetch_and(&rp2350_open_drain_mask, ~rp2350_gpio_pin_mask(pin));
            break;
        case GPIOx_TYPE_OPENDRAIN:
            atomic_fetch_or(&rp2350_open_drain_mask, rp2350_gpio_pin_mask(pin));
            break;
        default:
            return K_ERROR_INVPARAM;
    }

    return rp2350_gpio_sync_sio_output(pin);
}

kstatus_t gpio_set_af(uint8_t gpio_port_id, uint8_t pin, gpio_af_t af)
{
    kstatus_t status;
    uint32_t funcsel = (uint32_t)af;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    if (unlikely(funcsel > RP2350_GPIO_FUNCSEL_MAX)) {
        return K_ERROR_INVPARAM;
    }

    return rp2350_gpio_update_ctrl(pin, RP2350_GPIO_CTRL_FUNCSEL_MSK,
                                   (funcsel << RP2350_GPIO_CTRL_FUNCSEL_POS));
}

kstatus_t gpio_set_speed(uint8_t gpio_port_id, uint8_t pin, gpio_speed_t speed)
{
    kstatus_t status;
    uint32_t set_mask = 0u;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    switch (speed) {
        case GPIOx_SPEED_LOW:
            set_mask = (0u << RP2350_PADS_GPIO_DRIVE_POS);
            break;
        case GPIOx_SPEED_MEDIUM:
            set_mask = (1u << RP2350_PADS_GPIO_DRIVE_POS);
            break;
        case GPIOx_SPEED_HIGH:
            set_mask = (2u << RP2350_PADS_GPIO_DRIVE_POS) | RP2350_PADS_GPIO_SLEWFAST;
            break;
        case GPIOx_SPEED_VERY_HIGH:
            set_mask = (3u << RP2350_PADS_GPIO_DRIVE_POS) | RP2350_PADS_GPIO_SLEWFAST;
            break;
        default:
            return K_ERROR_INVPARAM;
    }

    return rp2350_gpio_update_pad(pin,
                                  RP2350_PADS_GPIO_DRIVE_MSK | RP2350_PADS_GPIO_SLEWFAST,
                                  set_mask);
}

kstatus_t gpio_set(uint8_t gpio_port_id, uint8_t pin)
{
    kstatus_t status;
    uint32_t pin_mask;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    pin_mask = rp2350_gpio_pin_mask(pin);
    status = rp2350_gpio_write_sio(RP2350_SIO_GPIO_OUT_SET_REG, pin_mask);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    if (rp2350_gpio_is_open_drain(pin)) {
        return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_CLR_REG, pin_mask);
    }

    return K_STATUS_OKAY;
}

kstatus_t gpio_reset(uint8_t gpio_port_id, uint8_t pin)
{
    kstatus_t status;
    uint32_t pin_mask;

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    pin_mask = rp2350_gpio_pin_mask(pin);
    status = rp2350_gpio_write_sio(RP2350_SIO_GPIO_OUT_CLR_REG, pin_mask);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    if (rp2350_gpio_is_open_drain(pin)) {
        return rp2350_gpio_write_sio(RP2350_SIO_GPIO_OE_SET_REG, pin_mask);
    }

    return K_STATUS_OKAY;
}

kstatus_t gpio_get(uint8_t gpio_port_id, uint8_t pin, bool *val)
{
    kstatus_t status;
    uint32_t reg;

    if (unlikely(val == NULL)) {
        return K_ERROR_INVPARAM;
    }

    status = rp2350_gpio_validate(gpio_port_id, pin);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    status = rp2350_gpio_read_sio(RP2350_SIO_GPIO_IN_REG, &reg);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    *val = ((reg & rp2350_gpio_pin_mask(pin)) != 0u);
    return K_STATUS_OKAY;
}
