// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/rng/rng.h>

#include <sentry/ktypes.h>

kstatus_t rng_probe(void)
{
    return K_STATUS_OKAY;
}

kstatus_t rng_get(uint32_t *random)
{
    if (unlikely(random == NULL)) {
        return K_ERROR_INVPARAM;
    }
    *random = 0;
    return K_STATUS_OKAY;
}
