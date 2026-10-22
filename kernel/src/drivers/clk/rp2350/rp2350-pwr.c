// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/clk/pwr.h>

#include <sentry/ktypes.h>

kstatus_t pwr_probe(void)
{
    return K_STATUS_OKAY;
}

kstatus_t pwr_set_voltage_regulator_scaling(uint8_t scale)
{
    /* RP2350 has no software-controlled voltage scaling in this driver path. */
    if (unlikely(scale != 0u)) {
        return K_ERROR_INVPARAM;
    }
    return K_STATUS_OKAY;
}
