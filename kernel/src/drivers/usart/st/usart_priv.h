// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __DRIVERS_USART_PRIV_H
#define __DRIVERS_USART_PRIV_H

#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>

/* XXX: might be soc agnostic */
#include "stm32-usart-dt.h"

static inline kstatus_t usart_map(void)
{
    stm32_usartport_desc_t const * usart_desc = stm32_usartport_get_desc();
    return mgr_mm_map_kdev(usart_desc->base_addr, usart_desc->size);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t usart_unmap(void) {
    return mgr_mm_unmap_kdev();
}

void usart_setup(const stm32_usartport_desc_t *usart);
kstatus_t usart_set_baudrate(const stm32_usartport_desc_t *usart);
kstatus_t usart_enable(const stm32_usartport_desc_t *usart);
kstatus_t usart_disable(const stm32_usartport_desc_t *usart);
void usart_tx_enable(const stm32_usartport_desc_t *usart);
void usart_tx_disable(const stm32_usartport_desc_t *usart);
void usart_wait_for_tx_empty(const stm32_usartport_desc_t *usart);
void usart_wait_for_tx_done(const stm32_usartport_desc_t *usart);
void usart_putc(const stm32_usartport_desc_t *usart, uint8_t c);

#endif /* __DRIVERS_USART_PRIV_H */
