// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx Flash Interface Controller driver (see ST RM0090 datasheet Table 1, Section 3)
 */

#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>
#include <bsp/drivers/flash/flash.h>

#include "flash_defs.h"
#include "stm32-flash-dt.h"

#define STM32F4_FLASH_W8_STATE_TIMEOUT 0x100UL

static inline kstatus_t flash_map(void)
{
    stm32_fmc_desc_t const * desc = stm32_fmc_get_desc(0);
    return mgr_mm_map_kdev(desc->base_addr, desc->size);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t flash_unmap(void) {
    return mgr_mm_unmap_kdev();
}

kstatus_t flash_probe(void)
{

    uint32_t acr;
    uint32_t wait_state_status;
    stm32_fmc_desc_t const * fmc_desc = stm32_fmc_get_desc(0); /* TODO: only flash0 supported by now */
    const uint32_t wait_state = (fmc_desc->wait_state << FLASH_ACR_LATENCY_SHIFT) & FLASH_ACR_LATENCY_MASK;
    uint32_t count = 0UL;
    kstatus_t status = K_STATUS_OKAY;

    if (unlikely((status = flash_map()) != K_STATUS_OKAY)) {
        goto err;
    }

    acr = ioread32(FLASH_BASE_ADDR + FLASH_ACR_REG);
    acr &= ~(FLASH_ACR_LATENCY_MASK);
    acr |= wait_state;
    iowrite32(FLASH_BASE_ADDR + FLASH_ACR_REG, acr);

    do {
        wait_state_status = ioread32(FLASH_BASE_ADDR + FLASH_ACR_REG) & FLASH_ACR_LATENCY_MASK;
        count++;
    } while ((wait_state != wait_state_status) && (count < STM32F4_FLASH_W8_STATE_TIMEOUT));

    if (unlikely(wait_state != wait_state_status)) {
        status = K_ERROR_NOTREADY;
    }
    flash_unmap();
err:
    return status;
}
