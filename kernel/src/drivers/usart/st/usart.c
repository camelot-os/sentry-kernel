// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file usart block lightweight support for logging (Tx) only
 * Only if kernel built in debug mode and UART identifier selected
 *
 * As this is a simple debugging usart, this driver is made to support
 * only the usage 8bits word, 1 start bit, n stop bit (8n1) configuration.
 * As a consequence, usart_rx and usart_tx manipuate uint8_t data only.
 */

#include <sentry/ktypes.h>
#if defined(CONFIG_ARCH_ARM_CORTEX_M)
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/irq_defs.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/buses.h>
#elif defined(CONFIG_ARCH_RV32)
//TODO: set missing headers
#else
#error "unsupported architecture!"
#endif
#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/usart/usart.h>
#include <bsp/drivers/gpio/gpio.h>
#include <sentry/io.h>

#include "usart_priv.h"
#include "stm32-usart-dt.h"

/**
 * @brief sending data over USART
 */
/*@
  requires \valid_read(data + (0 .. data_len-1));
  requires data_len > 0;
*/
kstatus_t usart_tx(const uint8_t *data, size_t data_len)
{
    kstatus_t status = K_STATUS_OKAY;
    stm32_usartport_desc_t const *usart = stm32_usartport_get_desc();
    size_t emitted = 0;

    if (unlikely((status = usart_map()) != K_STATUS_OKAY)) {
        goto err;
    }

    usart_set_baudrate(usart);
    usart_enable(usart);
    usart_tx_enable(usart);

    /* transmission loop */
    do {
        usart_wait_for_tx_empty(usart);
        usart_putc(usart, data[emitted]);
        emitted++;
    } while (emitted < data_len);

    usart_wait_for_tx_done(usart);
    usart_tx_disable(usart);
    usart_disable(usart);
    status = usart_unmap();

err:
    return status;
}

kstatus_t usart_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    stm32_usartport_desc_t const * usart = stm32_usartport_get_desc();
    size_t pin;
    // size_t usart_base = usart->base_addr;

    /* other IPs mapping is under other IP responsability */
    rcc_enable(usart->bus_id, usart->clk_msk, RCC_NOFLAG);
    for (pin = 0; pin < usart->pinctrl_tbl_size; pin++) {
        status = gpio_pinctrl_configure(usart->pinctrl_tbl[pin]);
        if (unlikely(status != K_STATUS_OKAY)) {
            goto err;
        }
    }
    /* map usart before manipulating it */
    if (unlikely((status = usart_map()) != K_STATUS_OKAY)) {
        goto err;
    }

    usart_setup(usart);
    usart_unmap();

err:
    return status;
}
