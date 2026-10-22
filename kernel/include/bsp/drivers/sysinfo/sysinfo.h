// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#ifndef DRV_SYSINFO_H
#define DRV_SYSINFO_H

#include <inttypes.h>

#include <sentry/ktypes.h>

/**
 * @file SYSINFO hardware kernel public API.
 */

kstatus_t sysinfo_get_chip_id(uint32_t *chip_id);

kstatus_t sysinfo_get_chip_revision(uint8_t *revision);

/* Compatibility helper: keeps existing call sites working. */
uint8_t sysinfo_chip_version(void);

#endif /* DRV_SYSINFO_H */
