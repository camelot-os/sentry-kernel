// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>
#include <sentry/io.h>

#include "opentitan_uart.h"

static inline kstatus_t usart_map(void)
{
    // TODO: get size from DTS
    return mgr_mm_map_kdev(UART_BASE, 0x1000);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t usart_unmap(void) {
    return mgr_mm_unmap_kdev();
}

kstatus_t usart_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;

    return 0;
}

#define CLK_FIXED_FREQ_HZ (50ULL * 1000 * 1000)

/**
 * @brief Init uart for TX only
 * 
 * Do not use interrupts for now
 */
static inline void uart_tx_init(unsigned int baud)
{
    uint64_t uart_ctrl_nco = ((uint64_t) baud << 20) / CLK_FIXED_FREQ_HZ;

    iowrite32(UART_CTRL, (
        ((uart_ctrl_nco & UART_CTRL_NCO_MSK) << UART_CTRL_NCO) |
        (1 << UART_CTRL_TX_EN)
    ));
}

static inline int uart_tx_rdy(void)
{
    return ((ioread32(UART_STATUS) & UART_TX_FULL) ? 0 : 1);
}

int uart_tx_empty(void)
{
    return ((ioread32(UART_STATUS) & UART_TX_EMPTY) ? 0 : 1);
}

kstatus_t usart_tx(const uint8_t *data, size_t data_len)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t emitted = 0;

    if (unlikely((status = usart_map()) != K_STATUS_OKAY)) {
        goto err;
    }

    uart_tx_init(96000);

    /* transmission loop */
    do {
        while (!uart_tx_rdy()) ;
        iowrite32(UART_WDATA, data[emitted]);
        emitted++;
    } while (emitted < data_len);

    while (!uart_tx_empty()) ;

    // Disable uart
    iowrite32(UART_CTRL, 0);

    status = usart_unmap();

err:
    return status;
}
