// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/gpio/gpio.h>
#include <bsp/drivers/usart/usart.h>

#include <sentry/io.h>
#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>

#if defined(CONFIG_SOC_SUBFAMILY_RP2350)
#include <sentry/arch/asm-cortex-m/buses.h>
#endif

#include "rp2350-usart-dt.h"

#ifndef BUSES_H
typedef enum bus_identifier {
    BUS_GENERIC = 0,
} bus_id_t;

#define BUS_IS_VALID(bus) (true)
#endif

#define RP2350_UART_DR_REG       0x000u
#define RP2350_UART_FR_REG       0x018u
#define RP2350_UART_IBRD_REG     0x024u
#define RP2350_UART_FBRD_REG     0x028u
#define RP2350_UART_LCR_H_REG    0x02cu
#define RP2350_UART_CR_REG       0x030u

#define RP2350_UART_FR_BUSY      (1u << 3)
#define RP2350_UART_FR_TXFF      (1u << 5)

#define RP2350_UART_LCR_H_FEN    (1u << 4)
#define RP2350_UART_LCR_H_WLEN_8 ((uint32_t)0x3u << 5)

#define RP2350_UART_CR_UARTEN    (1u << 0)
#define RP2350_UART_CR_TXE       (1u << 8)

static inline kstatus_t usart_map(const rp2350_usart_desc_t *usart)
{
    if (unlikely(usart == NULL)) {
        return K_ERROR_INVPARAM;
    }

    return mgr_mm_map_kdev(usart->base_addr, usart->size);
}

static inline kstatus_t usart_unmap(void)
{
    return mgr_mm_unmap_kdev();
}

static void rp2350_usart_disable(const rp2350_usart_desc_t *usart)
{
    iowrite32(usart->base_addr + RP2350_UART_CR_REG, 0u);
}

static void rp2350_usart_enable_tx(const rp2350_usart_desc_t *usart)
{
    iowrite32(usart->base_addr + RP2350_UART_CR_REG, RP2350_UART_CR_UARTEN | RP2350_UART_CR_TXE);
}

static void rp2350_usart_wait_tx_ready(const rp2350_usart_desc_t *usart)
{
    while ((ioread32(usart->base_addr + RP2350_UART_FR_REG) & RP2350_UART_FR_TXFF) != 0u) {
    }
}

static void rp2350_usart_wait_tx_done(const rp2350_usart_desc_t *usart)
{
    while ((ioread32(usart->base_addr + RP2350_UART_FR_REG) & RP2350_UART_FR_BUSY) != 0u) {
    }
}

static kstatus_t rp2350_usart_set_baudrate(const rp2350_usart_desc_t *usart)
{
    kstatus_t status;
    uint32_t uart_clk_hz;
    uint32_t baudrate;
    uint64_t divisor_x64;
    uint32_t integer_div;
    uint32_t fractional_div;

    baudrate = usart->baudrate;
    if (baudrate == 0u) {
        baudrate = 115200u;
    }

    status = rcc_get_bus_clock(BUS_GENERIC, &uart_clk_hz);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    divisor_x64 = (((uint64_t)uart_clk_hz) * 4u + (uint64_t)(baudrate / 2u)) / (uint64_t)baudrate;
    integer_div = (uint32_t)(divisor_x64 / 64u);
    fractional_div = (uint32_t)(divisor_x64 % 64u);

    if (unlikely(integer_div == 0u)) {
        return K_ERROR_INVPARAM;
    }

    iowrite32(usart->base_addr + RP2350_UART_IBRD_REG, integer_div);
    iowrite32(usart->base_addr + RP2350_UART_FBRD_REG, fractional_div);

    return K_STATUS_OKAY;
}

static void rp2350_usart_setup(const rp2350_usart_desc_t *usart)
{
    rp2350_usart_disable(usart);
    iowrite32(usart->base_addr + RP2350_UART_LCR_H_REG, RP2350_UART_LCR_H_WLEN_8 | RP2350_UART_LCR_H_FEN);
}

kstatus_t usart_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    const rp2350_usart_desc_t *usart = rp2350_usart_get_desc();
    size_t pin;

    if (unlikely(usart == NULL)) {
        return K_ERROR_INVPARAM;
    }

    status = rcc_enable(BUS_GENERIC, usart->reset_line, RCC_NOFLAG);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    for (pin = 0; pin < usart->pinctrl_tbl_size; pin++) {
        status = gpio_pinctrl_configure(usart->pinctrl_tbl[pin]);
        if (unlikely(status != K_STATUS_OKAY)) {
            return status;
        }
    }

    status = usart_map(usart);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    rp2350_usart_setup(usart);
    status = usart_unmap();

    return status;
}

kstatus_t usart_tx(const uint8_t *data, size_t data_len)
{
    kstatus_t status = K_STATUS_OKAY;
    const rp2350_usart_desc_t *usart = rp2350_usart_get_desc();
    size_t emitted = 0u;

    if (unlikely((data == NULL) || (data_len == 0u) || (usart == NULL))) {
        return K_ERROR_INVPARAM;
    }

    status = usart_map(usart);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }

    status = rp2350_usart_set_baudrate(usart);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto out;
    }

    rp2350_usart_enable_tx(usart);

    do {
        rp2350_usart_wait_tx_ready(usart);
        iowrite32(usart->base_addr + RP2350_UART_DR_REG, data[emitted]);
        emitted++;
    } while (emitted < data_len);

    rp2350_usart_wait_tx_done(usart);
    rp2350_usart_disable(usart);

out:
    if (usart_unmap() != K_STATUS_OKAY && status == K_STATUS_OKAY) {
        status = K_ERROR_DENIED;
    }

    return status;
}
