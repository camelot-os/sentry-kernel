// Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
// Copyright (c) 2025 H2Lab Development Team
// SPDX-License-Identifier: BSD-3-Clause

/**
 *
 * @file This file is part of the Raspberry Pi Pico SDK, and has been modified in order to
 * be included in the kernel.
 */

#include <bsp/drivers/sysinfo/sysinfo.h>

#include <sentry/io.h>
#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>

#define SYSINFO_BASE                  0x40000000UL
#define SYSINFO_REGISTER_WINDOW_SIZE  0x20UL
#define SYSINFO_CHIP_ID_REG           0x00UL

#define SYSINFO_CHIP_ID_REVISION_BITS 0xF0000000UL
#define SYSINFO_CHIP_ID_REVISION_LSB  28U

static kstatus_t sysinfo_read_chip_id(uint32_t *chip_id)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(chip_id == NULL)) {
        goto end;
    }

    status = mgr_mm_map_kdev(SYSINFO_BASE, SYSINFO_REGISTER_WINDOW_SIZE);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }

    *chip_id = ioread32(SYSINFO_BASE + SYSINFO_CHIP_ID_REG);

    status = mgr_mm_unmap_kdev();

end:
    return status;
}

kstatus_t sysinfo_get_chip_id(uint32_t *chip_id)
{
    return sysinfo_read_chip_id(chip_id);
}

kstatus_t sysinfo_get_chip_revision(uint8_t *revision)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t chip_id = 0u;

    if (unlikely(revision == NULL)) {
        goto end;
    }

    status = sysinfo_read_chip_id(&chip_id);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }

    *revision = (uint8_t)((chip_id & SYSINFO_CHIP_ID_REVISION_BITS) >> SYSINFO_CHIP_ID_REVISION_LSB);

end:
    return status;
}

uint8_t sysinfo_chip_version(void)
{
    uint8_t version = 0u;

    if (unlikely(sysinfo_get_chip_revision(&version) != K_STATUS_OKAY)) {
        return 0u;
    }
    return version;
}
