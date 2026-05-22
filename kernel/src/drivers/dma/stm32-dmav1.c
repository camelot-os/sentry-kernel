// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

/**
 * \file General purpose DMA driver for STM32F4xx (stm32-dmav1 compatible) SoCs
 */

#include <stdbool.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/io.h>
#include <bsp/drivers/dma/gpdma.h>
#include <bsp/drivers/clk/rcc.h>
#include "stm32-st-dmav1-dt.h"

/** @name STM32 DMA v1 global register offsets */
/** @{ */
#define STM32_DMA_LISR_REG        0x00UL
#define STM32_DMA_HISR_REG        0x04UL
#define STM32_DMA_LIFCR_REG       0x08UL
#define STM32_DMA_HIFCR_REG       0x0CUL
/** @} */

/** @name STM32 DMA v1 stream register offsets */
/** @{ */
#define STM32_DMA_SxCR(s)         (0x10UL + (0x18UL * (s)))
#define STM32_DMA_SxNDTR(s)       (0x14UL + (0x18UL * (s)))
#define STM32_DMA_SxPAR(s)        (0x18UL + (0x18UL * (s)))
#define STM32_DMA_SxM0AR(s)       (0x1CUL + (0x18UL * (s)))
#define STM32_DMA_SxM1AR(s)       (0x20UL + (0x18UL * (s)))
#define STM32_DMA_SxFCR(s)        (0x24UL + (0x18UL * (s)))
/** @} */

/** @name STM32 DMA v1 stream control bits */
/** @{ */
#define STM32_DMA_SxCR_EN         (1UL << 0)
#define STM32_DMA_SxCR_DMEIE      (1UL << 1)
#define STM32_DMA_SxCR_TEIE       (1UL << 2)
#define STM32_DMA_SxCR_HTIE       (1UL << 3)
#define STM32_DMA_SxCR_TCIE       (1UL << 4)
#define STM32_DMA_SxCR_DIR_SHIFT  6UL
#define STM32_DMA_SxCR_DIR_MASK   (0x3UL << STM32_DMA_SxCR_DIR_SHIFT)
#define STM32_DMA_SxCR_CIRC       (1UL << 8)
#define STM32_DMA_SxCR_PINC       (1UL << 9)
#define STM32_DMA_SxCR_MINC       (1UL << 10)
#define STM32_DMA_SxCR_PSIZE_SHIFT 11UL
#define STM32_DMA_SxCR_PSIZE_MASK (0x3UL << STM32_DMA_SxCR_PSIZE_SHIFT)
#define STM32_DMA_SxCR_MSIZE_SHIFT 13UL
#define STM32_DMA_SxCR_MSIZE_MASK (0x3UL << STM32_DMA_SxCR_MSIZE_SHIFT)
#define STM32_DMA_SxCR_PL_SHIFT   16UL
#define STM32_DMA_SxCR_PL_MASK    (0x3UL << STM32_DMA_SxCR_PL_SHIFT)
#define STM32_DMA_SxCR_CHSEL_SHIFT 25UL
#define STM32_DMA_SxCR_CHSEL_MASK (0x7UL << STM32_DMA_SxCR_CHSEL_SHIFT)
/** @} */

#define STM32_DMA_SxFCR_FEIE      (1UL << 7)

/** @name DMA transfer direction encoding for SxCR.DIR */
/** @{ */
#define STM32_DMA_DIR_PERIPH_TO_MEM 0UL
#define STM32_DMA_DIR_MEM_TO_PERIPH 1UL
#define STM32_DMA_DIR_MEM_TO_MEM    2UL
/** @} */

/** @name Per-stream status bits extracted from LISR/HISR */
/** @{ */
#define STM32_DMA_STATUS_FLAG_FEIF  (1UL << 0)
#define STM32_DMA_STATUS_FLAG_DMEIF (1UL << 1)
#define STM32_DMA_STATUS_FLAG_TEIF  (1UL << 2)
#define STM32_DMA_STATUS_FLAG_HTIF  (1UL << 3)
#define STM32_DMA_STATUS_FLAG_TCIF  (1UL << 4)
/** @} */

/**
 * @brief Mapping table from stream index to flag bit-shift in LISR/HISR.
 */
static const uint32_t stm32_dma_stream_flag_shift[8] = {
    0UL, 6UL, 16UL, 22UL, 0UL, 6UL, 16UL, 22UL,
};

/**
 * @brief Validate a DMA descriptor and resolve its controller descriptor.
 *
 * @param[in] desc DMA stream configuration descriptor.
 * @param[out] ctrl Resolved controller descriptor on success.
 *
 * @retval true Descriptor is valid and @p ctrl is initialized.
 * @retval false Invalid argument, unknown controller, or channel out of range.
 */
static inline bool stm32_dmav1_is_valid_desc(gpdma_stream_cfg_t const * const desc,
                                              stm32_gpdma_desc_t const ** const ctrl)
{
    if (unlikely((desc == NULL) || (ctrl == NULL))) {
        return false;
    }
    *ctrl = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(*ctrl == NULL)) {
        return false;
    }
    if (unlikely(desc->channel >= (*ctrl)->num_chan)) {
        return false;
    }
    return true;
}

/**
 * @brief Extract the 5 status bits associated with one stream from ISR.
 *
 * @param[in] stream Stream index (0..7).
 * @param[in] isr Raw ISR register value (LISR or HISR).
 *
 * @return Right-aligned stream status flags.
 */
static inline uint32_t stm32_dmav1_get_stream_raw_flags(uint8_t stream, uint32_t isr)
{
    uint32_t const shift = stm32_dma_stream_flag_shift[stream];
    return (isr >> shift) & 0x1FUL;
}

/**
 * @brief Build IFCR clear mask for one stream.
 *
 * @param[in] stream Stream index (0..7).
 *
 * @return Bitmask to write in LIFCR/HIFCR for this stream.
 */
static inline uint32_t stm32_dmav1_get_stream_clr_flags(uint8_t stream)
{
    uint32_t const shift = stm32_dma_stream_flag_shift[stream];
    return (0x1FUL << shift);
}

/**
 * @brief Convert generic beat length to STM32 DMA v1 register encoding.
 *
 * @param[in] beat Generic beat length value.
 *
 * @return Encoded beat value (0..2), or 0xFFFFFFFFUL if unsupported.
 */
static inline uint32_t stm32_dmav1_get_beat_cfg(uint8_t beat)
{
    uint32_t cfg = 0;

    switch (beat) {
        case GPDMA_BEAT_LEN_BYTE:
            cfg = 0;
            break;
        case GPDMA_BEAT_LEN_HALFWORD:
            cfg = 1;
            break;
        case GPDMA_BEAT_LEN_WORD:
            cfg = 2;
            break;
        default:
            cfg = 0xFFFFFFFFUL;
            break;
    }
    return cfg;
}

/**
 * @brief Convert generic beat length to byte size.
 *
 * @param[in] beat Generic beat length value.
 *
 * @return Beat size in bytes, or 0 if unsupported.
 */
static inline uint32_t stm32_dmav1_get_beat_size(uint8_t beat)
{
    uint32_t sz = 0;

    switch (beat) {
        case GPDMA_BEAT_LEN_BYTE:
            sz = 1UL;
            break;
        case GPDMA_BEAT_LEN_HALFWORD:
            sz = 2UL;
            break;
        case GPDMA_BEAT_LEN_WORD:
            sz = 4UL;
            break;
        default:
            sz = 0UL;
            break;
    }
    return sz;
}

/**
 * @brief Clear all status flags associated with one stream.
 *
 * @param[in] ctrl DMA controller descriptor.
 * @param[in] stream Stream index.
 */
static inline void stm32_dmav1_clear_stream_flags(stm32_gpdma_desc_t const * const ctrl,
                                                   uint8_t stream)
{
    uint32_t const clr = stm32_dmav1_get_stream_clr_flags(stream);

    if (stream < 4U) {
        iowrite32(ctrl->base_addr + STM32_DMA_LIFCR_REG, clr);
    } else {
        iowrite32(ctrl->base_addr + STM32_DMA_HIFCR_REG, clr);
    }
}


/**
 * @brief Probe and initialize one STM32 DMA v1 controller.
 *
 * Enables the RCC clock, maps the controller, clears pending flags,
 * and resets all stream registers to a known state.
 *
 * @param[in] controller DMA controller identifier.
 *
 * @retval K_STATUS_OKAY Controller initialized.
 * @retval K_ERROR_INVPARAM Invalid controller or mapping failure.
 * @retval Any error returned by RCC API on clock enable failure.
 */
kstatus_t stm32_dmav1_probe(uint8_t controller)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * const ctrl_desc = stm32_gpdma_get_desc(controller);
    uint8_t stream;

    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    status = rcc_enable(ctrl_desc->bus_id, ctrl_desc->clk_msk, RCC_NOFLAG);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }

    if (unlikely(gpdma_map(controller) != K_STATUS_OKAY)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }

    /* Clear all pending stream flags for a clean initial state. */
    iowrite32(ctrl_desc->base_addr + STM32_DMA_LIFCR_REG, 0x0F7D0F7DUL);
    iowrite32(ctrl_desc->base_addr + STM32_DMA_HIFCR_REG, 0x0F7D0F7DUL);

    for (stream = 0; stream < ctrl_desc->num_chan; ++stream) {
        iowrite32(ctrl_desc->base_addr + STM32_DMA_SxCR(stream), 0);
        iowrite32(ctrl_desc->base_addr + STM32_DMA_SxNDTR(stream), 0);
        iowrite32(ctrl_desc->base_addr + STM32_DMA_SxPAR(stream), 0);
        iowrite32(ctrl_desc->base_addr + STM32_DMA_SxM0AR(stream), 0);
        iowrite32(ctrl_desc->base_addr + STM32_DMA_SxM1AR(stream), 0);
        iowrite32(ctrl_desc->base_addr + STM32_DMA_SxFCR(stream), 0);
    }

    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief Clear status flags for one configured stream.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Flags cleared.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav1_channel_clear_status(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;

    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    stm32_dmav1_clear_stream_flags(ctrl, desc->channel);
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief Read runtime status for one DMA stream.
 *
 * @param[in] desc DMA stream descriptor.
 * @param[out] status Output status snapshot.
 *
 * @retval K_STATUS_OKAY Status returned in @p status.
 * @retval K_ERROR_INVPARAM Invalid argument or map failure.
 */
kstatus_t stm32_dmav1_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status)
{
    kstatus_t kret = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;
    uint32_t isr;
    uint32_t flags;
    uint32_t cr;

    if (unlikely((desc == NULL) || (status == NULL))) {
        goto end;
    }
    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    memset(status, 0, sizeof(*status));
    if (desc->channel < 4U) {
        isr = ioread32(ctrl->base_addr + STM32_DMA_LISR_REG);
    } else {
        isr = ioread32(ctrl->base_addr + STM32_DMA_HISR_REG);
    }
    flags = stm32_dmav1_get_stream_raw_flags(desc->channel, isr);
    cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));

    status->half_reached = !!(flags & STM32_DMA_STATUS_FLAG_HTIF);
    status->completed = !!(flags & STM32_DMA_STATUS_FLAG_TCIF);

    if (flags & (STM32_DMA_STATUS_FLAG_TEIF | STM32_DMA_STATUS_FLAG_DMEIF | STM32_DMA_STATUS_FLAG_FEIF)) {
        status->state = GPDMA_STATE_TRANSMISSION_FAILURE;
    } else if (flags & STM32_DMA_STATUS_FLAG_TCIF) {
        status->state = GPDMA_STATE_TRANSFER_COMPLETE;
    } else if (flags & STM32_DMA_STATUS_FLAG_HTIF) {
        status->state = GPDMA_STATE_HALF_TRANSFER;
    } else if (cr & STM32_DMA_SxCR_EN) {
        status->state = GPDMA_STATE_RUNNING;
    } else {
        status->state = GPDMA_STATE_IDLE;
    }

    gpdma_unmap();
    kret = K_STATUS_OKAY;
end:
    return kret;
}

/**
 * @brief Configure one DMA stream from a generic descriptor.
 *
 * The stream remains disabled after this call. Use
 * stm32_dmav1_channel_enable() to start the transfer.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Stream configured.
 * @retval K_ERROR_BADSTATE Stream currently enabled.
 * @retval K_ERROR_INVPARAM Invalid parameters or unsupported mode.
 */
kstatus_t stm32_dmav1_channel_configure(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;
    uint32_t cr = 0;
    uint32_t fcr = 0;
    uint32_t dir = 0;
    uint32_t psize;
    uint32_t msize;
    uint32_t src_size;
    uint32_t dst_size;
    size_t periph_addr;
    size_t mem_addr;
    uint32_t ndtr;

    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(desc->stream >= 8U)) {
        goto end;
    }
    if (unlikely(desc->is_triggered)) {
        goto end;
    }

    psize = stm32_dmav1_get_beat_cfg(desc->src_beat_len);
    msize = stm32_dmav1_get_beat_cfg(desc->dest_beat_len);
    src_size = stm32_dmav1_get_beat_size(desc->src_beat_len);
    dst_size = stm32_dmav1_get_beat_size(desc->dest_beat_len);

    if (unlikely((psize == 0xFFFFFFFFUL) || (msize == 0xFFFFFFFFUL) || (src_size == 0UL) || (dst_size == 0UL))) {
        goto end;
    }
    if (unlikely(src_size != dst_size)) {
        goto end;
    }
    if (unlikely((desc->transfer_len == 0UL) || ((desc->transfer_len % src_size) != 0UL))) {
        goto end;
    }
    ndtr = (uint32_t)(desc->transfer_len / src_size);
    if (unlikely((ndtr == 0UL) || (ndtr > 0xFFFFUL))) {
        goto end;
    }

    switch (desc->transfer_type) {
        case GPDMA_TRANSFER_MEMORY_TO_DEVICE:
            dir = STM32_DMA_DIR_MEM_TO_PERIPH;
            psize = stm32_dmav1_get_beat_cfg(desc->dest_beat_len);
            msize = stm32_dmav1_get_beat_cfg(desc->src_beat_len);
            periph_addr = desc->dest;
            mem_addr = desc->source;
            break;
        case GPDMA_TRANSFER_DEVICE_TO_MEMORY:
            dir = STM32_DMA_DIR_PERIPH_TO_MEM;
            psize = stm32_dmav1_get_beat_cfg(desc->src_beat_len);
            msize = stm32_dmav1_get_beat_cfg(desc->dest_beat_len);
            periph_addr = desc->source;
            mem_addr = desc->dest;
            break;
        case GPDMA_TRANSFER_MEMORY_TO_MEMORY:
            dir = STM32_DMA_DIR_MEM_TO_MEM;
            psize = stm32_dmav1_get_beat_cfg(desc->src_beat_len);
            msize = stm32_dmav1_get_beat_cfg(desc->dest_beat_len);
            periph_addr = desc->source;
            mem_addr = desc->dest;
            break;
        default:
            goto end;
    }

    if (unlikely((psize == 0xFFFFFFFFUL) || (msize == 0xFFFFFFFFUL))) {
        goto end;
    }

    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));
    if (unlikely((cr & STM32_DMA_SxCR_EN) != 0UL)) {
        status = K_ERROR_BADSTATE;
        goto unmap_end;
    }

    stm32_dmav1_clear_stream_flags(ctrl, desc->channel);

    cr = 0;
    cr |= ((desc->stream & 0x7UL) << STM32_DMA_SxCR_CHSEL_SHIFT);
    cr |= ((dir & 0x3UL) << STM32_DMA_SxCR_DIR_SHIFT);
    cr |= ((psize & 0x3UL) << STM32_DMA_SxCR_PSIZE_SHIFT);
    cr |= ((msize & 0x3UL) << STM32_DMA_SxCR_MSIZE_SHIFT);
    cr |= ((desc->priority & 0x3UL) << STM32_DMA_SxCR_PL_SHIFT);

    if (desc->circular_source || desc->circular_dest) {
        cr |= STM32_DMA_SxCR_CIRC;
    }

    if (desc->transfer_type == GPDMA_TRANSFER_MEMORY_TO_DEVICE) {
        if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_DEST) != 0U) {
            cr |= STM32_DMA_SxCR_PINC;
        }
        if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_SRC) != 0U) {
            cr |= STM32_DMA_SxCR_MINC;
        }
    } else {
        if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_SRC) != 0U) {
            cr |= STM32_DMA_SxCR_PINC;
        }
        if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_DEST) != 0U) {
            cr |= STM32_DMA_SxCR_MINC;
        }
    }

    if ((desc->interrupts & GPDMA_INT_TC) != 0U) {
        cr |= STM32_DMA_SxCR_TCIE;
    }
    if ((desc->interrupts & GPDMA_INT_HT) != 0U) {
        cr |= STM32_DMA_SxCR_HTIE;
    }
    if ((desc->interrupts & GPDMA_INT_ERROR) != 0U) {
        cr |= STM32_DMA_SxCR_TEIE | STM32_DMA_SxCR_DMEIE;
        fcr |= STM32_DMA_SxFCR_FEIE;
    }

    iowrite32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel), cr);
    iowrite32(ctrl->base_addr + STM32_DMA_SxNDTR(desc->channel), ndtr);
    iowrite32(ctrl->base_addr + STM32_DMA_SxPAR(desc->channel), (uint32_t)periph_addr);
    iowrite32(ctrl->base_addr + STM32_DMA_SxM0AR(desc->channel), (uint32_t)mem_addr);
    iowrite32(ctrl->base_addr + STM32_DMA_SxM1AR(desc->channel), 0);
    iowrite32(ctrl->base_addr + STM32_DMA_SxFCR(desc->channel), fcr);

    status = K_STATUS_OKAY;
unmap_end:
    gpdma_unmap();
end:
    return status;
}

/**
 * @brief Enable a previously configured DMA stream.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Stream enabled.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav1_channel_enable(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;
    uint32_t cr;

    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));
    cr |= STM32_DMA_SxCR_EN;
    iowrite32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel), cr);

    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief Get IRQ number associated with a DMA stream.
 *
 * @param[in] desc DMA stream descriptor.
 * @param[out] IRQn Interrupt number associated with this stream.
 *
 * @retval K_STATUS_OKAY IRQ number returned.
 * @retval K_ERROR_INVPARAM Invalid argument.
 */
kstatus_t stm32_dmav1_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;

    if (unlikely((desc == NULL) || (IRQn == NULL))) {
        goto end;
    }
    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    *IRQn = ctrl->interrupts[desc->channel];
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief Clear DMA interrupt source for one stream.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @return Same status as stm32_dmav1_channel_clear_status().
*/
kstatus_t stm32_dmav1_interrupt_clear(gpdma_stream_cfg_t const * const desc)
{
    return stm32_dmav1_channel_clear_status(desc);
}

/**
 * @brief Suspend a running stream by clearing its EN bit.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Stream suspended.
 * @retval K_ERROR_BADSTATE Stream not running or hardware did not stop.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav1_channel_suspend(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;
    uint32_t cr;
    uint32_t retry = 100000UL;

    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));
    if ((cr & STM32_DMA_SxCR_EN) == 0UL) {
        status = K_ERROR_BADSTATE;
        goto unmap_end;
    }

    cr &= ~STM32_DMA_SxCR_EN;
    iowrite32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel), cr);

    do {
        cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));
        if ((cr & STM32_DMA_SxCR_EN) == 0UL) {
            status = K_STATUS_OKAY;
            goto unmap_end;
        }
        --retry;
    } while (retry > 0UL);

    status = K_ERROR_BADSTATE;
unmap_end:
    gpdma_unmap();
end:
    return status;
}

/**
 * @brief Resume a previously suspended stream.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Stream resumed.
 * @retval K_ERROR_BADSTATE Stream already enabled.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav1_channel_resume(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;
    uint32_t cr;

    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));
    if ((cr & STM32_DMA_SxCR_EN) != 0UL) {
        status = K_ERROR_BADSTATE;
        goto unmap_end;
    }

    cr |= STM32_DMA_SxCR_EN;
    iowrite32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel), cr);
    status = K_STATUS_OKAY;

unmap_end:
    gpdma_unmap();
end:
    return status;
}

/**
 * @brief Reset stream registers and clear its status flags.
 *
 * The stream must be disabled before reset.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Stream reset.
 * @retval K_ERROR_BADSTATE Stream still enabled.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav1_channel_reset(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;
    uint32_t cr;

    if (unlikely(!stm32_dmav1_is_valid_desc(desc, &ctrl))) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }

    cr = ioread32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel));
    if ((cr & STM32_DMA_SxCR_EN) != 0UL) {
        status = K_ERROR_BADSTATE;
        goto unmap_end;
    }

    stm32_dmav1_clear_stream_flags(ctrl, desc->channel);
    iowrite32(ctrl->base_addr + STM32_DMA_SxCR(desc->channel), 0);
    iowrite32(ctrl->base_addr + STM32_DMA_SxNDTR(desc->channel), 0);
    iowrite32(ctrl->base_addr + STM32_DMA_SxPAR(desc->channel), 0);
    iowrite32(ctrl->base_addr + STM32_DMA_SxM0AR(desc->channel), 0);
    iowrite32(ctrl->base_addr + STM32_DMA_SxM1AR(desc->channel), 0);
    iowrite32(ctrl->base_addr + STM32_DMA_SxFCR(desc->channel), 0);

    status = K_STATUS_OKAY;
unmap_end:
    gpdma_unmap();
end:
    return status;
}

/* aliasing functions to generic API */
kstatus_t gpdma_probe(uint8_t controller) __attribute__((alias("stm32_dmav1_probe")));
kstatus_t gpdma_channel_clear_status(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav1_channel_clear_status")));
kstatus_t gpdma_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status) __attribute__((alias("stm32_dmav1_channel_get_status")));
kstatus_t gpdma_channel_configure(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav1_channel_configure")));
kstatus_t gpdma_channel_enable(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav1_channel_enable")));
kstatus_t gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn) __attribute__((alias("stm32_dmav1_get_interrupt")));
kstatus_t gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc) __attribute__((alias("stm32_dmav1_interrupt_clear")));
kstatus_t gpdma_channel_suspend(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav1_channel_suspend")));
kstatus_t gpdma_channel_resume(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav1_channel_resume")));
kstatus_t gpdma_channel_reset(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav1_channel_reset")));
