// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32 I/O Muxer and EXTI driver
 */

#include <bsp/drivers/gpio/pinctrl.h>

#include "stm32-gpio-dt.h"
#include "gpio_defs.h"

kstatus_t gpio_pinctrl_configure(gpio_pinctrl_desc_t pinctrl_desc)
{
    kstatus_t status = K_STATUS_OKAY;

    if (unlikely(pinctrl_desc.port_id >= GPIO_INVALID_PORT_ID)) {
        status = K_ERROR_INVPARAM;
        goto ret;
    }

    /* XXX: fixme !!! generate this limit !!! */
    if (unlikely(pinctrl_desc.pin >= 16)) {
        status = K_ERROR_INVPARAM;
        goto ret;
    }
    /* TODO: this will generates a lot of map/unmap. Maybe using head functions
     * for mapping or a flag to avoid useless consecutive map/unmap here
     */
    gpio_set_af(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.altfunc);
    gpio_set_type(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.type);
    gpio_set_speed(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.speed);
    gpio_set_pull_mode(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.pull_mode);
    gpio_set_mode(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.mode);

ret:
    return status;
}
