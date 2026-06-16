// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/exti/exti.h>

#include <sentry/ktypes.h>

kstatus_t exti_probe(void)
{
    return K_STATUS_OKAY;
}

kstatus_t exti_mask_interrupt(uint8_t itn)
{
    (void)itn;
    return K_STATUS_OKAY;
}

kstatus_t exti_unmask_interrupt(uint8_t itn)
{
    (void)itn;
    return K_STATUS_OKAY;
}

kstatus_t exti_mask_event(uint8_t evn)
{
    (void)evn;
    return K_STATUS_OKAY;
}

kstatus_t exti_unmask_event(uint8_t evn)
{
    (void)evn;
    return K_STATUS_OKAY;
}

kstatus_t exti_generate_swinterrupt(uint8_t itn)
{
    (void)itn;
    return K_STATUS_OKAY;
}

kstatus_t exti_clear_pending(uint8_t itn)
{
    (void)itn;
    return K_STATUS_OKAY;
}
