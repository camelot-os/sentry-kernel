// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/gpio/pinctrl.h>

#include <sentry/ktypes.h>

kstatus_t gpio_pinctrl_configure(gpio_pinctrl_desc_t pinctrl_desc)
{
    kstatus_t status;

    status = gpio_set_type(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.type);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    status = gpio_set_speed(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.speed);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    status = gpio_set_pull_mode(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.pull_mode);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    if (pinctrl_desc.mode == GPIOx_MODE_AF) {
        status = gpio_set_af(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.altfunc);
        if (unlikely(status != K_STATUS_OKAY)) {
            return status;
        }
    }

    return gpio_set_mode(pinctrl_desc.port_id, pinctrl_desc.pin, pinctrl_desc.mode);
}
