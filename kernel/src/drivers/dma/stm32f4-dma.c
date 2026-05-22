// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file General purpose DMA driver for STM32F4xx (stm32-dma-v1 compatible) SoCs
 */

#include <stdbool.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/io.h>
#include <bsp/drivers/dma/gpdma.h>
#include <bsp/drivers/clk/rcc.h>
#include "stm32-dma-dt.h"


/**
 * @brief probe given GPDMA controller identifier
 */
kstatus_t gpdma_probe(uint8_t controller)
{
    return K_STATUS_OKAY;
}

/**
 * @brief clear given channel status flags
 */
kstatus_t gpdma_channel_clear_status(gpdma_stream_cfg_t const*const desc)
{
    return K_STATUS_OKAY;
}

/**
 * @brief get back current status of given DMA descriptor's stream
 */
kstatus_t gpdma_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status)
{
    return K_STATUS_OKAY;
}

/**
 * @brief configure a DMA channel with given DMA descriptor
 *
 * @note this function do not enable the DMA channel, but only configure it
 */
kstatus_t gpdma_channel_configure(gpdma_stream_cfg_t const*const desc)
{
    return K_STATUS_OKAY;
}

/**
 * @brief enable a previously configured DMA channel
 */
kstatus_t gpdma_channel_enable(gpdma_stream_cfg_t const*const desc)
{
    return K_STATUS_OKAY;
}

/**
 * @brief given a stream, get back the associated IRQn
 */
kstatus_t gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn)
{
    return K_STATUS_OKAY;
}

/**
 * @brief clear interrupt of corresponding stream at GPDMA level
*/
kstatus_t gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc)
{
    return K_STATUS_OKAY;
}

/**
 * @brief suspend currently started stream
 */
kstatus_t gpdma_channel_suspend(gpdma_stream_cfg_t const*const desc)
{
    return K_STATUS_OKAY;
}

/**
 * @brief resume previously suspended stream
 */
kstatus_t gpdma_channel_resume(gpdma_stream_cfg_t const*const desc)
{
    return K_STATUS_OKAY;
}

/**
 * @brief reset currently suspended stream
 */
kstatus_t gpdma_channel_reset(gpdma_stream_cfg_t const*const desc)
{
    return K_STATUS_OKAY;
}
