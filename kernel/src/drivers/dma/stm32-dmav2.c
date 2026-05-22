// SPDX-FileCopyrightText: 2026 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file General purpose DMA driver for STM32 (stm32-dmav2 compatible) SoCs
 */

#include <stdbool.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/io.h>
#include <bsp/drivers/dma/gpdma.h>
#include <bsp/drivers/clk/rcc.h>
#include "stm32-st-dmav2-dt.h"

/** @name STM32 DMA v2 global register offsets */
/** @{ */
#define STM32_DMA_ISR_REG            0x00UL
#define STM32_DMA_IFCR_REG           0x04UL
/** @} */

/** @name STM32 DMA v2 channel register offsets */
/** @{ */
#define STM32_DMA_CCR(c)             (0x08UL + (0x14UL * (c)))
#define STM32_DMA_CNDTR(c)           (0x0CUL + (0x14UL * (c)))
#define STM32_DMA_CPAR(c)            (0x10UL + (0x14UL * (c)))
#define STM32_DMA_CMAR(c)            (0x14UL + (0x14UL * (c)))
#define STM32_DMA_CSELR_REG          0xA8UL
/** @} */

/** @name STM32 DMA v2 CCR bit definitions */
/** @{ */
#define STM32_DMA_CCR_EN             (1UL << 0)
#define STM32_DMA_CCR_TCIE           (1UL << 1)
#define STM32_DMA_CCR_HTIE           (1UL << 2)
#define STM32_DMA_CCR_TEIE           (1UL << 3)
#define STM32_DMA_CCR_DIR            (1UL << 4)
#define STM32_DMA_CCR_CIRC           (1UL << 5)
#define STM32_DMA_CCR_PINC           (1UL << 6)
#define STM32_DMA_CCR_MINC           (1UL << 7)
#define STM32_DMA_CCR_PSIZE_SHIFT    8UL
#define STM32_DMA_CCR_MSIZE_SHIFT    10UL
#define STM32_DMA_CCR_PL_SHIFT       12UL
#define STM32_DMA_CCR_MEM2MEM        (1UL << 14)
/** @} */

/** @name Per-channel status bits (4-bit field in ISR/IFCR) */
/** @{ */
#define STM32_DMA_STATUS_FLAG_GIF    (1UL << 0)
#define STM32_DMA_STATUS_FLAG_TCIF   (1UL << 1)
#define STM32_DMA_STATUS_FLAG_HTIF   (1UL << 2)
#define STM32_DMA_STATUS_FLAG_TEIF   (1UL << 3)
/** @} */

/** @name STM32 DMA v2 request multiplexer helpers */
/** @{ */
#define STM32_DMA_CSELR_CxS_SHIFT(c) (4UL * (c))
#define STM32_DMA_CSELR_CxS_MASK(c)  (0xFUL << STM32_DMA_CSELR_CxS_SHIFT(c))
/** @} */

/**
 * @brief Validate a DMA descriptor and resolve its controller descriptor.
 *
 * @param[in] desc DMA stream configuration descriptor.
 * @param[out] ctrl Resolved controller descriptor on success.
 *
 * @retval true Descriptor is valid and @p ctrl is initialized.
 * @retval false Invalid argument, unknown controller, or channel out of range.
 */
static inline bool stm32_dmav2_is_valid_desc(gpdma_stream_cfg_t const * const desc,
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
 * @brief Extract one channel status nibble from ISR value.
 *
 * @param[in] channel DMA channel index.
 * @param[in] isr Raw ISR value.
 *
 * @return Right-aligned 4-bit status flags for the channel.
 */
static inline uint32_t stm32_dmav2_get_chan_raw_flags(uint8_t channel, uint32_t isr)
{
	uint32_t const shift = 4UL * channel;
	return (isr >> shift) & 0xFUL;
}

/**
 * @brief Build the IFCR clear mask for one channel.
 *
 * @param[in] channel DMA channel index.
 *
 * @return Channel clear mask positioned in the global IFCR register.
 */
static inline uint32_t stm32_dmav2_get_chan_clr_flags(uint8_t channel)
{
	uint32_t const shift = 4UL * channel;
	return (0xFUL << shift);
}

/**
 * @brief Convert generic beat length to STM32 DMA v2 register encoding.
 *
 * @param[in] beat Generic beat length value.
 *
 * @return Encoded beat value (0..2), or 0xFFFFFFFFUL if unsupported.
 */
static inline uint32_t stm32_dmav2_get_beat_cfg(uint8_t beat)
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
static inline uint32_t stm32_dmav2_get_beat_size(uint8_t beat)
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
 * @brief Clear all status flags for one channel.
 *
 * @param[in] ctrl DMA controller descriptor.
 * @param[in] channel DMA channel index.
 */
static inline void stm32_dmav2_clear_channel_flags(stm32_gpdma_desc_t const * const ctrl,
							    uint8_t channel)
{
	iowrite32(ctrl->base_addr + STM32_DMA_IFCR_REG,
		 stm32_dmav2_get_chan_clr_flags(channel));
}

/**
 * @brief Probe and initialize one STM32 DMA v2 controller.
 *
 * Enables the RCC clock, maps controller registers, clears pending flags,
 * resets all channel registers, and resets request mux mapping.
 *
 * @param[in] controller DMA controller identifier.
 *
 * @retval K_STATUS_OKAY Controller initialized.
 * @retval K_ERROR_INVPARAM Invalid controller or map failure.
 * @retval Any error returned by RCC API on clock enable failure.
 */
kstatus_t stm32_dmav2_probe(uint8_t controller)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * const ctrl_desc = stm32_gpdma_get_desc(controller);
	uint8_t channel;

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

	/* Clear all pending flags then reset channels and request mappings. */
	for (channel = 0; channel < ctrl_desc->num_chan; ++channel) {
		stm32_dmav2_clear_channel_flags(ctrl_desc, channel);
		iowrite32(ctrl_desc->base_addr + STM32_DMA_CCR(channel), 0);
		iowrite32(ctrl_desc->base_addr + STM32_DMA_CNDTR(channel), 0);
		iowrite32(ctrl_desc->base_addr + STM32_DMA_CPAR(channel), 0);
		iowrite32(ctrl_desc->base_addr + STM32_DMA_CMAR(channel), 0);
	}
	iowrite32(ctrl_desc->base_addr + STM32_DMA_CSELR_REG, 0);

	gpdma_unmap();
	status = K_STATUS_OKAY;
end:
	return status;
}

/**
 * @brief Clear status flags for one configured channel.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Flags cleared.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav2_channel_clear_status(gpdma_stream_cfg_t const*const desc)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;

	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	stm32_dmav2_clear_channel_flags(ctrl, desc->channel);
	gpdma_unmap();
	status = K_STATUS_OKAY;
end:
	return status;
}

/**
 * @brief Read runtime status for one DMA channel.
 *
 * @param[in] desc DMA stream descriptor.
 * @param[out] status Output status snapshot.
 *
 * @retval K_STATUS_OKAY Status returned in @p status.
 * @retval K_ERROR_INVPARAM Invalid argument or map failure.
 */
kstatus_t stm32_dmav2_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status)
{
	kstatus_t kret = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;
	uint32_t isr;
	uint32_t flags;
	uint32_t ccr;

	if (unlikely((desc == NULL) || (status == NULL))) {
		goto end;
	}
	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	memset(status, 0, sizeof(*status));
	isr = ioread32(ctrl->base_addr + STM32_DMA_ISR_REG);
	flags = stm32_dmav2_get_chan_raw_flags(desc->channel, isr);
	ccr = ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel));

	status->half_reached = !!(flags & STM32_DMA_STATUS_FLAG_HTIF);
	status->completed = !!(flags & STM32_DMA_STATUS_FLAG_TCIF);

	if (flags & STM32_DMA_STATUS_FLAG_TEIF) {
		status->state = GPDMA_STATE_TRANSMISSION_FAILURE;
	} else if (flags & STM32_DMA_STATUS_FLAG_TCIF) {
		status->state = GPDMA_STATE_TRANSFER_COMPLETE;
	} else if (flags & STM32_DMA_STATUS_FLAG_HTIF) {
		status->state = GPDMA_STATE_HALF_TRANSFER;
	} else if (ccr & STM32_DMA_CCR_EN) {
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
 * @brief Configure one DMA channel from a generic descriptor.
 *
 * The channel remains disabled after this call. Use
 * stm32_dmav2_channel_enable() to start the transfer.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Channel configured.
 * @retval K_ERROR_BADSTATE Channel currently enabled.
 * @retval K_ERROR_INVPARAM Invalid parameters or unsupported mode.
 */
kstatus_t stm32_dmav2_channel_configure(gpdma_stream_cfg_t const*const desc)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;
	uint32_t ccr = 0;
	uint32_t cselr;
	uint32_t psize;
	uint32_t msize;
	uint32_t src_size;
	uint32_t dst_size;
	size_t periph_addr;
	size_t mem_addr;
	uint32_t ndtr;

	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(desc->is_triggered)) {
		goto end;
	}
	if (unlikely(desc->transfer_type == GPDMA_TRANSFER_DEVICE_TO_DEVICE)) {
		goto end;
	}

	psize = stm32_dmav2_get_beat_cfg(desc->src_beat_len);
	msize = stm32_dmav2_get_beat_cfg(desc->dest_beat_len);
	src_size = stm32_dmav2_get_beat_size(desc->src_beat_len);
	dst_size = stm32_dmav2_get_beat_size(desc->dest_beat_len);

	if (unlikely((psize == 0xFFFFFFFFUL) || (msize == 0xFFFFFFFFUL) ||
			     (src_size == 0UL) || (dst_size == 0UL))) {
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
			psize = stm32_dmav2_get_beat_cfg(desc->dest_beat_len);
			msize = stm32_dmav2_get_beat_cfg(desc->src_beat_len);
			periph_addr = desc->dest;
			mem_addr = desc->source;
			ccr |= STM32_DMA_CCR_DIR;
			break;
		case GPDMA_TRANSFER_DEVICE_TO_MEMORY:
			psize = stm32_dmav2_get_beat_cfg(desc->src_beat_len);
			msize = stm32_dmav2_get_beat_cfg(desc->dest_beat_len);
			periph_addr = desc->source;
			mem_addr = desc->dest;
			break;
		case GPDMA_TRANSFER_MEMORY_TO_MEMORY:
			psize = stm32_dmav2_get_beat_cfg(desc->src_beat_len);
			msize = stm32_dmav2_get_beat_cfg(desc->dest_beat_len);
			periph_addr = desc->source;
			mem_addr = desc->dest;
			ccr |= STM32_DMA_CCR_MEM2MEM;
			break;
		default:
			goto end;
	}

	if (unlikely((psize == 0xFFFFFFFFUL) || (msize == 0xFFFFFFFFUL))) {
		goto end;
	}
	if (unlikely(desc->stream >= ctrl->num_req)) {
		goto end;
	}

	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	if (unlikely((ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel)) & STM32_DMA_CCR_EN) != 0UL)) {
		status = K_ERROR_BADSTATE;
		goto unmap_end;
	}

	stm32_dmav2_clear_channel_flags(ctrl, desc->channel);

	ccr |= ((psize & 0x3UL) << STM32_DMA_CCR_PSIZE_SHIFT);
	ccr |= ((msize & 0x3UL) << STM32_DMA_CCR_MSIZE_SHIFT);
	ccr |= ((desc->priority & 0x3UL) << STM32_DMA_CCR_PL_SHIFT);

	if (desc->circular_source || desc->circular_dest) {
		ccr |= STM32_DMA_CCR_CIRC;
	}

	if (desc->transfer_type == GPDMA_TRANSFER_MEMORY_TO_DEVICE) {
		if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_DEST) != 0U) {
			ccr |= STM32_DMA_CCR_PINC;
		}
		if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_SRC) != 0U) {
			ccr |= STM32_DMA_CCR_MINC;
		}
	} else {
		if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_SRC) != 0U) {
			ccr |= STM32_DMA_CCR_PINC;
		}
		if ((desc->transfer_mode & GPDMA_TRANSFER_MODE_INCREMENT_DEST) != 0U) {
			ccr |= STM32_DMA_CCR_MINC;
		}
	}

	if ((desc->interrupts & GPDMA_INT_TC) != 0U) {
		ccr |= STM32_DMA_CCR_TCIE;
	}
	if ((desc->interrupts & GPDMA_INT_HT) != 0U) {
		ccr |= STM32_DMA_CCR_HTIE;
	}
	if ((desc->interrupts & GPDMA_INT_ERROR) != 0U) {
		ccr |= STM32_DMA_CCR_TEIE;
	}

	/* Program request multiplexer (4-bit request per channel). */
	cselr = ioread32(ctrl->base_addr + STM32_DMA_CSELR_REG);
	cselr &= ~STM32_DMA_CSELR_CxS_MASK(desc->channel);
	cselr |= (((uint32_t)desc->stream & 0xFUL) << STM32_DMA_CSELR_CxS_SHIFT(desc->channel));
	iowrite32(ctrl->base_addr + STM32_DMA_CSELR_REG, cselr);

	iowrite32(ctrl->base_addr + STM32_DMA_CCR(desc->channel), 0);
	iowrite32(ctrl->base_addr + STM32_DMA_CNDTR(desc->channel), ndtr);
	iowrite32(ctrl->base_addr + STM32_DMA_CPAR(desc->channel), (uint32_t)periph_addr);
	iowrite32(ctrl->base_addr + STM32_DMA_CMAR(desc->channel), (uint32_t)mem_addr);
	iowrite32(ctrl->base_addr + STM32_DMA_CCR(desc->channel), ccr);

	status = K_STATUS_OKAY;
unmap_end:
	gpdma_unmap();
end:
	return status;
}

/**
 * @brief Enable a previously configured DMA channel.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Channel enabled.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav2_channel_enable(gpdma_stream_cfg_t const*const desc)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;
	uint32_t ccr;

	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	ccr = ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel));
	ccr |= STM32_DMA_CCR_EN;
	iowrite32(ctrl->base_addr + STM32_DMA_CCR(desc->channel), ccr);

	gpdma_unmap();
	status = K_STATUS_OKAY;
end:
	return status;
}

/**
 * @brief Get IRQ number associated with one DMA channel.
 *
 * @param[in] desc DMA stream descriptor.
 * @param[out] IRQn Interrupt number associated with this channel.
 *
 * @retval K_STATUS_OKAY IRQ number returned.
 * @retval K_ERROR_INVPARAM Invalid argument.
 */
kstatus_t stm32_dmav2_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;

	if (unlikely((desc == NULL) || (IRQn == NULL))) {
		goto end;
	}
	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	*IRQn = ctrl->interrupts[desc->channel];
	status = K_STATUS_OKAY;
end:
	return status;
}

/**
 * @brief Clear DMA interrupt source for one channel.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @return Same status as stm32_dmav2_channel_clear_status().
 */
kstatus_t stm32_dmav2_interrupt_clear(gpdma_stream_cfg_t const * const desc)
{
	return stm32_dmav2_channel_clear_status(desc);
}

/**
 * @brief Suspend a running channel by clearing its EN bit.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Channel suspended.
 * @retval K_ERROR_BADSTATE Channel not running or hardware did not stop.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav2_channel_suspend(gpdma_stream_cfg_t const*const desc)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;
	uint32_t ccr;
	uint32_t retry = 100000UL;

	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	ccr = ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel));
	if ((ccr & STM32_DMA_CCR_EN) == 0UL) {
		status = K_ERROR_BADSTATE;
		goto unmap_end;
	}

	ccr &= ~STM32_DMA_CCR_EN;
	iowrite32(ctrl->base_addr + STM32_DMA_CCR(desc->channel), ccr);

	do {
		ccr = ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel));
		if ((ccr & STM32_DMA_CCR_EN) == 0UL) {
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
 * @brief Resume a previously suspended DMA channel.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Channel resumed.
 * @retval K_ERROR_BADSTATE Channel already enabled.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav2_channel_resume(gpdma_stream_cfg_t const*const desc)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;
	uint32_t ccr;

	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	ccr = ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel));
	if ((ccr & STM32_DMA_CCR_EN) != 0UL) {
		status = K_ERROR_BADSTATE;
		goto unmap_end;
	}

	ccr |= STM32_DMA_CCR_EN;
	iowrite32(ctrl->base_addr + STM32_DMA_CCR(desc->channel), ccr);
	status = K_STATUS_OKAY;
unmap_end:
	gpdma_unmap();
end:
	return status;
}

/**
 * @brief Reset channel registers and clear its status flags.
 *
 * The channel must be disabled before reset.
 *
 * @param[in] desc DMA stream descriptor.
 *
 * @retval K_STATUS_OKAY Channel reset.
 * @retval K_ERROR_BADSTATE Channel still enabled.
 * @retval K_ERROR_INVPARAM Invalid descriptor or map failure.
 */
kstatus_t stm32_dmav2_channel_reset(gpdma_stream_cfg_t const*const desc)
{
	kstatus_t status = K_ERROR_INVPARAM;
	stm32_gpdma_desc_t const * ctrl = NULL;
	uint32_t ccr;
	uint32_t cselr;

	if (unlikely(!stm32_dmav2_is_valid_desc(desc, &ctrl))) {
		goto end;
	}
	if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
		goto end;
	}

	ccr = ioread32(ctrl->base_addr + STM32_DMA_CCR(desc->channel));
	if ((ccr & STM32_DMA_CCR_EN) != 0UL) {
		status = K_ERROR_BADSTATE;
		goto unmap_end;
	}

	stm32_dmav2_clear_channel_flags(ctrl, desc->channel);
	iowrite32(ctrl->base_addr + STM32_DMA_CCR(desc->channel), 0);
	iowrite32(ctrl->base_addr + STM32_DMA_CNDTR(desc->channel), 0);
	iowrite32(ctrl->base_addr + STM32_DMA_CPAR(desc->channel), 0);
	iowrite32(ctrl->base_addr + STM32_DMA_CMAR(desc->channel), 0);

	cselr = ioread32(ctrl->base_addr + STM32_DMA_CSELR_REG);
	cselr &= ~STM32_DMA_CSELR_CxS_MASK(desc->channel);
	iowrite32(ctrl->base_addr + STM32_DMA_CSELR_REG, cselr);

	status = K_STATUS_OKAY;
unmap_end:
	gpdma_unmap();
end:
	return status;
}

/* aliasing functions to generic API */
kstatus_t gpdma_probe(uint8_t controller) __attribute__((alias("stm32_dmav2_probe")));
kstatus_t gpdma_channel_clear_status(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav2_channel_clear_status")));
kstatus_t gpdma_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status) __attribute__((alias("stm32_dmav2_channel_get_status")));
kstatus_t gpdma_channel_configure(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav2_channel_configure")));
kstatus_t gpdma_channel_enable(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav2_channel_enable")));
kstatus_t gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn) __attribute__((alias("stm32_dmav2_get_interrupt")));
kstatus_t gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc) __attribute__((alias("stm32_dmav2_interrupt_clear")));
kstatus_t gpdma_channel_suspend(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav2_channel_suspend")));
kstatus_t gpdma_channel_resume(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav2_channel_resume")));
kstatus_t gpdma_channel_reset(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32_dmav2_channel_reset")));
