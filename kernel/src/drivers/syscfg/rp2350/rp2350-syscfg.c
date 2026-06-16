// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/syscfg/syscfg.h>

#include <sentry/ktypes.h>

kstatus_t syscfg_probe(void)
{
    return K_STATUS_OKAY;
}

#ifdef CONFIG_HAS_FLASH_DUAL_BANK
kstatus_t syscfg_switch_bank(void)
{
    return K_ERROR_NOENT;
}
#endif

kstatus_t syscfg_set_exti(uint8_t gpio_pin_id, uint8_t gpio_port_id)
{
    (void)gpio_pin_id;
    (void)gpio_port_id;
    return K_STATUS_OKAY;
}