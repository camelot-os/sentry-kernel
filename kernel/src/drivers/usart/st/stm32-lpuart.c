// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file STM32 LPUART block lightweight support for logging (Tx) only
 * Only if kernel built in debug mode and UART identifier selected
 *
 * As this is a simple debugging uart, this driver is made to support
 * only the usage 8bits word, 1 start bit, n stop bit (8n1) configuration.
 * As a consequence, uart_rx and uart_tx manipuate uint8_t data only.
 */

#include <sentry/io.h>
#include <bsp/drivers/clk/rcc.h>

#include "lpuart_defs.h"
#include "usart_priv.h"
#include "stm32-usart-dt.h"

#if defined(LPUART_CR1_DISABLED_REG)
#define LPUART_CR1_REG LPUART_CR1_DISABLED_REG
#define LPUART_CR1_UE LPUART_CR1_DISABLED_UE
#define LPUART_CR1_TE LPUART_CR1_DISABLED_TE
#endif /* LPUART_CR1_DISABLED_REG */

#if defined(LPUART_ISR_DISABLED_REG)
#define LPUART_ISR_REG LPUART_ISR_DISABLED_REG
#define LPUART_ISR_TEACK LPUART_ISR_DISABLED_TEACK
#define LPUART_ISR_TXE LPUART_ISR_DISABLED_TXE
#define LPUART_ISR_TC LPUART_ISR_DISABLED_TC
#endif /* LPUART_ISR_DISABLED_REG */

static kstatus_t stm32_lpuart_enable(stm32_usartport_desc_t const *usart)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;

    reg = ioread32(usart->base_addr + LPUART_CR1_REG);
    reg |= LPUART_CR1_UE;
    iowrite32(usart->base_addr + LPUART_CR1_REG, reg);

    return status;
}

static kstatus_t stm32_lpuart_disable(stm32_usartport_desc_t const *usart)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;

    reg = ioread32(usart->base_addr + LPUART_CR1_REG);
    reg &= ~LPUART_CR1_UE;
    iowrite32(usart->base_addr + LPUART_CR1_REG, reg);

    return status;
}

static void __stm32_lpuart_wait_te_ack(stm32_usartport_desc_t const *usart, bool enable)
{
    /* XXX: if DISabled, poll until bit set, cleared if disabled */
    uint32_t val = enable ? 0 : LPUART_ISR_TEACK;
    while ((ioread32(usart->base_addr + LPUART_ISR_REG) & LPUART_ISR_TEACK) == val);
}

static void stm32_lpuart_tx_enable(stm32_usartport_desc_t const *usart)
{
    uint32_t cr1 = ioread32(usart->base_addr + LPUART_CR1_REG);
    cr1 |= LPUART_CR1_TE;
    iowrite32(usart->base_addr + LPUART_CR1_REG, cr1);
    __stm32_lpuart_wait_te_ack(usart, true);
}

static void stm32_lpuart_tx_disable(stm32_usartport_desc_t const *usart)
{
    uint32_t cr1 = ioread32(usart->base_addr + LPUART_CR1_REG);
    cr1 &= ~LPUART_CR1_TE;
    iowrite32(usart->base_addr + LPUART_CR1_REG, cr1);
    __stm32_lpuart_wait_te_ack(usart, false);
}

static void stm32_lpuart_wait_for_tx_empty(stm32_usartport_desc_t const *usart)
{
    while ((ioread32(usart->base_addr + LPUART_ISR_REG) & LPUART_ISR_TXE) == 0);
}

static void __stm32_lpuart_clear_tx_done(stm32_usartport_desc_t const *usart)
{
    iowrite32(usart->base_addr + LPUART_ICR_REG, LPUART_ICR_TCCF);
}

static void stm32_lpuart_wait_for_tx_done(stm32_usartport_desc_t const *usart)
{
    while ((ioread32(usart->base_addr + LPUART_ISR_REG) & LPUART_ISR_TC) == 0);
    __stm32_lpuart_clear_tx_done(usart);
}

static kstatus_t stm32_lpuart_set_baudrate(stm32_usartport_desc_t const *usart)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t usart_base = usart->base_addr;
    uint32_t lpuart_ker_clk;
    uint32_t baudrate = 115200;
    uint32_t lpuartdiv;

    if (unlikely((status = rcc_get_bus_clock(usart->bus_id, &lpuart_ker_clk)) != K_STATUS_OKAY)) {
        goto err;
    }

    /* XXX: read ker prescaler too, not needed for 115200 default baudrate */

    if (lpuart_ker_clk > 160000000) {
        lpuart_ker_clk /= 100;
        baudrate /= 100;
    }
    else if (lpuart_ker_clk > 16000000) {
        lpuart_ker_clk /= 10;
        baudrate /= 10;
    }

    lpuartdiv = DIV_ROUND_UP(lpuart_ker_clk << 8, baudrate);

    /* XXX: CF reference Manual LPUART chapter */
    if (lpuartdiv < 0x300) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    iowrite32(usart_base + LPUART_BRR_REG, lpuartdiv & LPUART_BRR_BRR_MASK);
err:
    return status;
}

static void stm32_lpuart_putc(const stm32_usartport_desc_t *usart, uint8_t c)
{
     iowrite32(usart->base_addr + LPUART_TDR_REG, c);
}

static void stm32_lpuart_setup(const stm32_usartport_desc_t *usart)
{
    /* Standard uart 8N1 configuration */
    iowrite32(usart->base_addr + LPUART_CR1_REG, 0x0UL);
    iowrite32(usart->base_addr + LPUART_CR2_REG, 0x0UL);
    iowrite32(usart->base_addr + LPUART_CR3_REG, 0x0UL);
}

kstatus_t usart_enable(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_enable")));
kstatus_t usart_disable(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_disable")));
void usart_tx_enable(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_tx_enable")));
void usart_tx_disable(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_tx_disable")));
void usart_wait_for_tx_empty(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_wait_for_tx_empty")));
void usart_wait_for_tx_done(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_wait_for_tx_done")));
kstatus_t usart_set_baudrate(stm32_usartport_desc_t const *usart) __attribute__((alias("stm32_lpuart_set_baudrate")));
void usart_putc(const stm32_usartport_desc_t *usart, uint8_t c) __attribute__((alias("stm32_lpuart_putc")));
void usart_setup(const stm32_usartport_desc_t *usart) __attribute__((alias("stm32_lpuart_setup")));
