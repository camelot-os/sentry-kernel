// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include <bsp/drivers/dma/gpdma.h>
#include <bsp/drivers/clk/rcc.h>

#include <dt-bindings/dma/rpi_pico_dma.h>
#include <sentry/ktypes.h>
#include <sentry/io.h>

#include "rp2350-gpdma-dt.h"

#define RP2350_DMA_CHAN_STRIDE          0x40u

#define RP2350_DMA_CH_READ_ADDR(ch)     (0x000u + (RP2350_DMA_CHAN_STRIDE * (ch)))
#define RP2350_DMA_CH_WRITE_ADDR(ch)    (0x004u + (RP2350_DMA_CHAN_STRIDE * (ch)))
#define RP2350_DMA_CH_TRANS_COUNT(ch)   (0x008u + (RP2350_DMA_CHAN_STRIDE * (ch)))
#define RP2350_DMA_CH_CTRL_TRIG(ch)     (0x00cu + (RP2350_DMA_CHAN_STRIDE * (ch)))

#define RP2350_DMA_INTR_REG             0x400u
#define RP2350_DMA_INTE_REG(irqidx)     (0x404u + (0x10u * (irqidx)))
#define RP2350_DMA_CHAN_ABORT_REG       0x444u

#define RP2350_DMA_CTRL_TRIG_EN         (1u << 0)
#define RP2350_DMA_CTRL_TRIG_HIGH_PRIO  (1u << 1)
#define RP2350_DMA_CTRL_TRIG_DATA_SIZE_POS 2u
#define RP2350_DMA_CTRL_TRIG_DATA_SIZE_MSK (0x3u << RP2350_DMA_CTRL_TRIG_DATA_SIZE_POS)
#define RP2350_DMA_CTRL_TRIG_INCR_READ  (1u << 4)
#define RP2350_DMA_CTRL_TRIG_INCR_WRITE (1u << 5)
#define RP2350_DMA_CTRL_TRIG_CHAIN_TO_POS 11u
#define RP2350_DMA_CTRL_TRIG_CHAIN_TO_MSK (0xfu << RP2350_DMA_CTRL_TRIG_CHAIN_TO_POS)
#define RP2350_DMA_CTRL_TRIG_TREQ_SEL_POS 15u
#define RP2350_DMA_CTRL_TRIG_TREQ_SEL_MSK (0x3fu << RP2350_DMA_CTRL_TRIG_TREQ_SEL_POS)
#define RP2350_DMA_CTRL_TRIG_BUSY       (1u << 24)
#define RP2350_DMA_CTRL_TRIG_WRITE_ERR  (1u << 29)
#define RP2350_DMA_CTRL_TRIG_READ_ERR   (1u << 30)
#define RP2350_DMA_CTRL_TRIG_AHB_ERR    (1u << 31)

static inline kstatus_t rp2350_gpdma_validate_stream_cfg(gpdma_stream_cfg_t const * const desc,
                                                          rp2350_gpdma_desc_t const **ctrl)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely((desc == NULL) || (ctrl == NULL))) {
        goto err;
    }

    *ctrl = rp2350_gpdma_get_desc(desc->controller);
    if (unlikely(*ctrl == NULL)) {
        status = K_ERROR_NOENT;
        goto err;
    }
    if (unlikely(desc->channel >= (*ctrl)->num_chan)) {
        goto err;
    }

    status = K_STATUS_OKAY;

err:
    return status;
}

static inline uint32_t rp2350_gpdma_channel_mask(uint16_t channel)
{
    return (1u << channel);
}

static inline uint16_t rp2350_gpdma_irq_index_for_channel(const rp2350_gpdma_desc_t *ctrl, uint16_t channel)
{
    uint16_t irq_idx = 0u;
    uint16_t channels_per_irq;

    if (unlikely((ctrl == NULL) || (ctrl->num_irq == 0u))) {
        goto err;
    }
    channels_per_irq = ctrl->num_chan / ctrl->num_irq;
    if (channels_per_irq == 0u) {
        channels_per_irq = 1u;
    }
    irq_idx = (uint16_t)(channel / channels_per_irq);

err:
    return irq_idx;
}

static inline kstatus_t rp2350_gpdma_decode_data_width(uint8_t beat_len, uint32_t *ctrl_val)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(ctrl_val == NULL)) {
        goto err;
    }

    switch (beat_len) {
        case GPDMA_BEAT_LEN_BYTE:
            *ctrl_val |= (0u << RP2350_DMA_CTRL_TRIG_DATA_SIZE_POS);
            break;
        case GPDMA_BEAT_LEN_HALFWORD:
            *ctrl_val |= (1u << RP2350_DMA_CTRL_TRIG_DATA_SIZE_POS);
            break;
        case GPDMA_BEAT_LEN_WORD:
            *ctrl_val |= (2u << RP2350_DMA_CTRL_TRIG_DATA_SIZE_POS);
            break;
        default:
            goto err;
    }

    status = K_STATUS_OKAY;

err:
    return status;
}

static inline kstatus_t rp2350_gpdma_get_beat_size(uint8_t beat_len, size_t *beat_size)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(beat_size == NULL)) {
        goto err;
    }

    switch (beat_len) {
        case GPDMA_BEAT_LEN_BYTE:
            *beat_size = 1u;
            break;
        case GPDMA_BEAT_LEN_HALFWORD:
            *beat_size = 2u;
            break;
        case GPDMA_BEAT_LEN_WORD:
            *beat_size = 4u;
            break;
        default:
            goto err;
    }

    status = K_STATUS_OKAY;

err:
    return status;
}

kstatus_t gpdma_probe(uint8_t controller)
{
    const rp2350_gpdma_desc_t *ctrl = rp2350_gpdma_get_desc(controller);
    kstatus_t status = K_ERROR_NOENT;
    bool mapped = false;

    if (unlikely(ctrl == NULL)) {
        goto err;
    }

    status = rcc_enable(BUS_GENERIC, ctrl->reset_line, RCC_NOFLAG);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }

    status = rp2350_gpdma_map(controller);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    iowrite32(ctrl->base_addr + RP2350_DMA_INTR_REG, 0xffffffffu);
    for (uint16_t irq_idx = 0; irq_idx < ctrl->num_irq; ++irq_idx) {
        iowrite32(ctrl->base_addr + RP2350_DMA_INTE_REG(irq_idx), 0u);
    }

    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}

kstatus_t gpdma_channel_clear_status(gpdma_stream_cfg_t const * const desc)
{
    const rp2350_gpdma_desc_t *ctrl;
    bool mapped = false;
    kstatus_t status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);

    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    iowrite32(ctrl->base_addr + RP2350_DMA_INTR_REG, rp2350_gpdma_channel_mask(desc->channel));
    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}

kstatus_t gpdma_channel_get_status(gpdma_stream_cfg_t const * const desc, gpdma_chan_status_t *status)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint32_t ctrl_trig;
    uint32_t trans_count;
    uint32_t pending;
    bool mapped = false;
    kstatus_t kret = K_ERROR_INVPARAM;

    if (unlikely(status == NULL)) {
        goto err;
    }
    *status = (gpdma_chan_status_t){ 0 };

    kret = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);
    if (unlikely(kret != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((kret = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    ctrl_trig = ioread32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel));
    trans_count = ioread32(ctrl->base_addr + RP2350_DMA_CH_TRANS_COUNT(desc->channel));
    pending = ioread32(ctrl->base_addr + RP2350_DMA_INTR_REG) & rp2350_gpdma_channel_mask(desc->channel);

    if ((ctrl_trig & (RP2350_DMA_CTRL_TRIG_AHB_ERR | RP2350_DMA_CTRL_TRIG_READ_ERR | RP2350_DMA_CTRL_TRIG_WRITE_ERR)) != 0u) {
        status->state = GPDMA_STATE_TRANSMISSION_FAILURE;
    }
    else if ((ctrl_trig & RP2350_DMA_CTRL_TRIG_BUSY) != 0u) {
        status->state = GPDMA_STATE_RUNNING;
    }
    else {
        status->state = GPDMA_STATE_IDLE;
    }

    if ((pending != 0u) || (trans_count == 0u && status->state == GPDMA_STATE_IDLE)) {
        status->completed = 1u;
    }

    kret = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return kret;
}

kstatus_t gpdma_channel_configure(gpdma_stream_cfg_t const * const desc)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint32_t ctrl_trig = 0u;
    uint16_t irq_idx;
    uint32_t irq_mask;
    size_t beat_size;
    size_t transfer_count;
    bool mapped = false;
    kstatus_t status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);

    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely(desc->transfer_len == 0u)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    status = rp2350_gpdma_decode_data_width(desc->dest_beat_len, &ctrl_trig);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely(desc->src_beat_len != desc->dest_beat_len)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    status = rp2350_gpdma_get_beat_size(desc->dest_beat_len, &beat_size);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((desc->transfer_len % beat_size) != 0u)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    transfer_count = desc->transfer_len / beat_size;
    if (unlikely(transfer_count == 0u || transfer_count > 0xffffffffu)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_SRC) != 0u) {
        ctrl_trig |= RP2350_DMA_CTRL_TRIG_INCR_READ;
    }
    if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_DEST) != 0u) {
        ctrl_trig |= RP2350_DMA_CTRL_TRIG_INCR_WRITE;
    }
    if (desc->priority >= GPDMA_PRIORITY_HIGH) {
        ctrl_trig |= RP2350_DMA_CTRL_TRIG_HIGH_PRIO;
    }

    ctrl_trig |= (((uint32_t)desc->channel << RP2350_DMA_CTRL_TRIG_CHAIN_TO_POS) & RP2350_DMA_CTRL_TRIG_CHAIN_TO_MSK);
    ctrl_trig |= (((uint32_t)RPI_PICO_DMA_SLOT_TO_DREQ(desc->stream) << RP2350_DMA_CTRL_TRIG_TREQ_SEL_POS) & RP2350_DMA_CTRL_TRIG_TREQ_SEL_MSK);

    if (unlikely((status = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    iowrite32(ctrl->base_addr + RP2350_DMA_INTR_REG, rp2350_gpdma_channel_mask(desc->channel));
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel), ctrl_trig);
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_READ_ADDR(desc->channel), (uint32_t)desc->source);
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_WRITE_ADDR(desc->channel), (uint32_t)desc->dest);
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_TRANS_COUNT(desc->channel), (uint32_t)transfer_count);

    irq_idx = rp2350_gpdma_irq_index_for_channel(ctrl, desc->channel);
    if (irq_idx < ctrl->num_irq) {
        irq_mask = ioread32(ctrl->base_addr + RP2350_DMA_INTE_REG(irq_idx));
        if (desc->interrupts != 0u) {
            irq_mask |= rp2350_gpdma_channel_mask(desc->channel);
        }
        else {
            irq_mask &= ~rp2350_gpdma_channel_mask(desc->channel);
        }
        iowrite32(ctrl->base_addr + RP2350_DMA_INTE_REG(irq_idx), irq_mask);
    }

    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}

kstatus_t gpdma_channel_enable(gpdma_stream_cfg_t const * const desc)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint32_t ctrl_trig;
    uint32_t trans_count;
    bool mapped = false;
    kstatus_t status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);

    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    trans_count = ioread32(ctrl->base_addr + RP2350_DMA_CH_TRANS_COUNT(desc->channel));
    if (trans_count == 0u) {
        status = K_ERROR_BADSTATE;
        goto err;
    }

    ctrl_trig = ioread32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel));
    ctrl_trig |= RP2350_DMA_CTRL_TRIG_EN;
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel), ctrl_trig);

    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}

kstatus_t gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint16_t irq_idx;
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(IRQn == NULL)) {
        goto err;
    }

    status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }

    irq_idx = rp2350_gpdma_irq_index_for_channel(ctrl, desc->channel);
    if (unlikely(irq_idx >= ctrl->num_irq)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    *IRQn = ctrl->interrupts[irq_idx];
    status = K_STATUS_OKAY;

err:
    return status;
}

bool gpdma_irq_is_dma_owned(uint16_t IRQn)
{
    return rp2350_gpdma_irq_is_dma_owned(IRQn);
}

kstatus_t gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc)
{
    kstatus_t status;

    status = gpdma_channel_clear_status(desc);

err:
    return status;
}

kstatus_t gpdma_channel_suspend(gpdma_stream_cfg_t const * const desc)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint32_t ctrl_trig;
    bool mapped = false;
    kstatus_t status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);

    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    ctrl_trig = ioread32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel));
    if ((ctrl_trig & RP2350_DMA_CTRL_TRIG_BUSY) == 0u) {
        status = K_ERROR_BADSTATE;
        goto err;
    }

    ctrl_trig &= ~RP2350_DMA_CTRL_TRIG_EN;
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel), ctrl_trig);

    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}

kstatus_t gpdma_channel_resume(gpdma_stream_cfg_t const * const desc)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint32_t ctrl_trig;
    uint32_t trans_count;
    bool mapped = false;
    kstatus_t status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);

    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    ctrl_trig = ioread32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel));
    trans_count = ioread32(ctrl->base_addr + RP2350_DMA_CH_TRANS_COUNT(desc->channel));

    if ((ctrl_trig & RP2350_DMA_CTRL_TRIG_BUSY) != 0u || trans_count == 0u) {
        status = K_ERROR_BADSTATE;
        goto err;
    }

    ctrl_trig |= RP2350_DMA_CTRL_TRIG_EN;
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel), ctrl_trig);

    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}

kstatus_t gpdma_channel_reset(gpdma_stream_cfg_t const * const desc)
{
    const rp2350_gpdma_desc_t *ctrl;
    uint32_t ctrl_trig;
    uint32_t timeout = 100000u;
    bool mapped = false;
    kstatus_t status = rp2350_gpdma_validate_stream_cfg(desc, &ctrl);

    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = rp2350_gpdma_map(desc->controller)) != K_STATUS_OKAY)) {
        goto err;
    }
    mapped = true;

    iowrite32(ctrl->base_addr + RP2350_DMA_CHAN_ABORT_REG, rp2350_gpdma_channel_mask(desc->channel));
    do {
        ctrl_trig = ioread32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel));
        if ((ctrl_trig & RP2350_DMA_CTRL_TRIG_BUSY) == 0u) {
            break;
        }
        timeout--;
    } while (timeout > 0u);

    if (timeout == 0u) {
        status = K_ERROR_BUSY;
        goto err;
    }

    iowrite32(ctrl->base_addr + RP2350_DMA_INTR_REG, rp2350_gpdma_channel_mask(desc->channel));
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_CTRL_TRIG(desc->channel), 0u);
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_READ_ADDR(desc->channel), 0u);
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_WRITE_ADDR(desc->channel), 0u);
    iowrite32(ctrl->base_addr + RP2350_DMA_CH_TRANS_COUNT(desc->channel), 0u);

    status = K_STATUS_OKAY;

err:
    if (mapped) {
        rp2350_gpdma_unmap();
    }
    return status;
}
