// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/smp/smp.h>

#include <sentry/ktypes.h>

kstatus_t smp_get_cpuid(size_t * const cpuid)
{
    if (unlikely(cpuid == NULL)) {
        return K_ERROR_INVPARAM;
    }
    *cpuid = 0;
    return K_STATUS_OKAY;
}
