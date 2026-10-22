// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/io.h>
#include <bsp/drivers/dma/gpdma.h>
#include <bsp/drivers/clk/rcc.h>
#include "stm32-gpdma-dt.h"
#include "gpdma_defs.h"

/**
 * NOTE: the SVD file is not properly written (using tables) and as
 * such all channel registers are declared and defined separately, while
 * they should have the same declaration for chan 0-11 and for chan 12-15.
 * As a consequence:
 *
 * Register access indexation is defined in the bellowing LU macros
 * Register structure used is 0 for chan 0-11, and 12 for 12-15, as
 * these two subsets behave the same
 */

/* 0-15 unified registers */
#define GPDMA_CxLBAR(x) (0x50+(0x80 * x))
#define GPDMA_CxFCR(x)  (0x5c+(0x80 * x))
#define GPDMA_CxSR(x)   (0x60+(0x80 * x))
#define GPDMA_CxCR(x)   (0x64+(0x80 * x))
#define GPDMA_CxTR1(x)  (0x90+(0x80 * x))
#define GPDMA_CxTR2(x)  (0x94+(0x80 * x))
#define GPDMA_CxLLR(x)  (0xcc+(0x80 * x))
/* existing but differenciated 0-11 vs 12-15 registers */
#define GPDMA_CxBR1(x)  (0x98+(0x80 * x))
/* 12-15 only registers */
#define GPDMA_CxSAR(x)  (0x9c+(0x80 * x))
#define GPDMA_CxDAR(x)  (0xa0+(0x80 * x))
#define GPDMA_CxTR3(x)  (0xa4+(0x80 * x))
#define GPDMA_CxBR2(x)  (0xa8+(0x80 * x))

/**
 * @brief register typing helper union
 *
 * used in order to allow ioread()/iowrite() of full register value
 * through raw type, while accessing register's fields using each register
 * field. All GPDMA register's are size_t (32b) length
 */
typedef union gpdma_register {
    size_t            raw;
    gpdma_seccfgr_t   seccfgr;
    gpdma_privcfgr_t  privcfgr;
    gpdma_misr_t      misr;
    gpdma_c0lbar_t    lbar;
    gpdma_c0fcr_t     cxfcr;
    gpdma_c0sr_t      cxsr;
    gpdma_c0cr_t      cxcr;
    gpdma_c0tr1_t     cxtr1;
    gpdma_c0tr2_t     cxtr2;
    gpdma_c0llr_t     cxllr;
    gpdma_c0br1_t     cxbr1_0_11;
    gpdma_c12br1_t    cxbr1_12_15;
    gpdma_c12sar_t    cxsar;
    gpdma_c12dar_t    cxdar;
    gpdma_c12tr3_t    cxtr3;
    gpdma_c12br2_t    cxbr2;
} gpdma_register_t;

/**
 * @fn get interrupt number associated to the given stream
 *
 * This function consider that the stream is strictly associated to a given {ctr,chan} couple,
 * and that each chan of a given controller has a strictly defined IRQ number. This is the case
 * of STM32U5 GPDMA controller.
 *
 * @param[in] desc: stream descriptor, has defined in gpdma.h and forged from DTS
 * @param[out] IRQn: IRQ number associated to the stream, when configured
 */
static kstatus_t stm32u5_gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl = NULL;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    if (unlikely(IRQn == NULL)) {
        goto end;
    }
    ctrl = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl == NULL)) {
        goto end;
    }
    *IRQn = ctrl->interrupts[desc->channel];
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn check given channel idle flag
 *
 * return true if the channel is idle, meaning:
 * - not configured
 * - disabled
 * - suspended
 */
/*@
 * requires (gpdma_controler_exists(ctrl) && gpdma_channel_is_valid(chanid));
 */
static  bool smt32u5_gpdma_is_channel_idle(uint8_t ctrl, uint16_t chanid)
{
    stm32_gpdma_desc_t const *desc = stm32_gpdma_get_desc(ctrl);

    uint32_t reg = ioread32(desc->base_addr + GPDMA_CxSR(chanid));
    reg &= 0x1; /* get back only IDLEF */

    return (!!reg);
}

/**
 * @fn clear GPDMA global interrupt
 *
 * clear both GPDMA interrupt status register for given channel and
 * NVIC related interrupt.
 *
 * This is the driver level clear
 */
kstatus_t stm32u5_gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const stm32_gpdma_desc_t * ctrl = NULL;

    uint16_t IRQn;
    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl == NULL)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    /* FCR is in write1_clear mode, clearing channel CR  */
    iowrite32(ctrl->base_addr + GPDMA_CxFCR(desc->channel), (0xF7FUL << 8));
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t stm32u5_gpdma_probe(uint8_t controller)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * const ctrl_desc = stm32_gpdma_get_desc(controller);
    gpdma_register_t reg;

    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    /* configure RCC line for GPDMA controller */
    if (unlikely((status = rcc_enable(ctrl_desc->bus_id, ctrl_desc->clk_msk, RCC_NOFLAG)) != K_STATUS_OKAY)) {
        goto end;
    }
    /** TODO: if needed, reset controller (soft reboot use case). Need issue #324 to be fixed first */

    /**
     * FIXME: note that we probe and configure chans in non-secure mode, while
     * secure boot (and secure mode) is not yet enabled for Sentry kernel.
     * When using secure mode, the secure configuration register must be set accordingly
     */
    /*
     * force channels to be unprivileged, as Sentry kernel do not use DMA chans for its own.
     * such a configuration avoid any userspace-to-kernelspace corruption, but do not permit
     * userspace-to-userspace corruption prevention.
     * as a consequence, all device and memory ranges accedded need to be checked at configure
     * time (by upper layers)
     */
    if (unlikely(gpdma_map(controller) != K_STATUS_OKAY)) {
        goto end;
    }
    reg.raw = 0;
    iowrite32(ctrl_desc->base_addr + GPDMA_PRIVCFGR_REG, reg.raw);
    gpdma_unmap();
    /**
     * NOTE: by now, we do not lock channels. We may consider unused channels to be locked, based on
     * DTS informations
     */

    status = K_STATUS_OKAY;
end:
    return status;
}


/*@
 * requires (gpdma_controler_exists(ctrl) && gpdma_channel_is_valid(chanid));
 */
kstatus_t smt32u5_gpdma_channel_clear_status(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    /* FCR is in write1_clear mode */
    iowrite32(ctrl_desc->base_addr + GPDMA_CxFCR(desc->channel), (0xF7FUL << 8));
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}


kstatus_t smt32u5_gpdma_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * statusf)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;
    gpdma_register_t cxsr;

    if (unlikely(desc == NULL) || statusf == NULL) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    cxsr.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxFCR(desc->channel));
    statusf->half_reached = !!cxsr.cxsr.htf;
    statusf->completed = !!cxsr.cxsr.tcf;
    if (!!cxsr.cxsr.idlef) {
        statusf->state = GPDMA_STATE_IDLE;
    }
    if (!!cxsr.cxsr.suspf) {
        statusf->state = GPDMA_STATE_SUSPENDED;
    }
    if (!!cxsr.cxsr.ulef || !!cxsr.cxsr.dtef) {
        statusf->state = GPDMA_STATE_TRANSMISSION_FAILURE;
    }
    if (!!cxsr.cxsr.usef) {
        statusf->state = GPDMA_STATE_CONFIGURATION_FAILURE;
    }
#if 0
    /** FIXME: the tof field (defined in datasheet) do not exist in SVD file */
    if (!!cxsr.sr.tof) {
        statusf->state = GPDMA_STATE_OVERRUN;
    }
#endif
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t stm32u5_gpdma_channel_configure(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;
    gpdma_register_t reg;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    if (unlikely(!smt32u5_gpdma_is_channel_idle(desc->controller, desc->channel))) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (desc->interrupts != 0) {
        reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_MISR_REG);
        /* allowing interrupts for this channel */
        reg.raw |= (0x1UL << desc->channel);
        iowrite32(ctrl_desc->base_addr + GPDMA_MISR_REG, reg.raw);
    }
    /* configure channel-local infos */
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel));
    if (desc->interrupts | GPDMA_INT_TC) {
        reg.cxcr.tcie = 1;
    }
    if (desc->interrupts | GPDMA_INT_HT) {
        reg.cxcr.htie = 1;
    }
    if (desc->interrupts | GPDMA_INT_ERROR) {
        reg.cxcr.uleie = 1;
        reg.cxcr.dteie = 1;
    }
    iowrite32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel), reg.raw);

    /* configuring transfer control register 1 */
    reg.raw = 0;
    reg.cxtr1.sbx = 0; /* no byte exchange */
    /* naive repartition between GPDMA 2 ports: low and medium to port 0, others to port 1 */
    if (desc->priority <= GPDMA_PRIORITY_MEDIUM) {
        reg.cxtr1.sap = 0; /* using bus access port 0 */
    } else {
        reg.cxtr1.sap = 1; /* using bus access port 1 */
    }
    switch (desc->dest_beat_len) {
        case GPDMA_BEAT_LEN_BYTE:
            reg.cxtr1.ddw_log2 = 0;
            break;
        case GPDMA_BEAT_LEN_HALFWORD:
            reg.cxtr1.ddw_log2 = 1;
            break;
        case GPDMA_BEAT_LEN_WORD:
            reg.cxtr1.ddw_log2 = 2;
            break;
        default:
            goto end;
    }
    switch (desc->src_beat_len) {
        case GPDMA_BEAT_LEN_BYTE:
            reg.cxtr1.sdw_log2 = 0;
            break;
        case GPDMA_BEAT_LEN_HALFWORD:
            reg.cxtr1.sdw_log2 = 1;
            break;
        case GPDMA_BEAT_LEN_WORD:
            reg.cxtr1.sdw_log2 = 2;
            break;
        default:
            goto end;
    }
    if (desc->transfer_mode == GPDMA_TRANSFER_MODE_INCREMENT_NONE) {
            reg.cxtr1.sinc = 0;
            reg.cxtr1.dinc = 0;
    }
    if (desc->transfer_mode | GPDMA_TRANSFER_MODE_INCREMENT_SRC) {
        reg.cxtr1.sinc = 1;
    }
    if (desc->transfer_mode | GPDMA_TRANSFER_MODE_INCREMENT_DEST) {
        reg.cxtr1.dinc = 1;
    }
    iowrite32(ctrl_desc->base_addr + GPDMA_CxTR1(desc->channel), reg.raw);

    /* configure CxTR2 */
    reg.raw = 0;
    if (desc->transfer_type == GPDMA_TRANSFER_MEMORY_TO_MEMORY) {
        reg.cxtr2.swreq = 1;
    } else {
        reg.cxtr2.reqsel = desc->stream;
    }
    if (desc->is_triggered) {
        reg.cxtr2.trigsel = (desc->trigger & (GPDMA_C0TR2_TRIGSEL_MASK >> GPDMA_C0TR2_TRIGSEL_SHIFT));
        reg.cxtr2.trigpol = 1; /* trigger on rising edge. NOTE: this is hard-coded by now */
    }
    reg.cxtr2.tcem = 3; /* trigger TC event at channel level */

    /**
     * lptim1_ue et lptim3_ue have HW req/ack at block level instead of burst level
     * See u5 RM0456 datasheet, Section 17.3.3
     */
    if (unlikely((desc->stream == 107) || (desc->stream == 113))) {
        reg.cxtr2.breq = 1;
    }
    reg.cxtr2.trigm = 3; /* channel level trigger granularity */
    iowrite32(ctrl_desc->base_addr + GPDMA_CxTR2(desc->channel), reg.raw);

    if (desc->transfer_len > (64*KBYTE)) {
        goto end;
    }
    reg.raw = 0;
    if (desc->stream <= 11) {
        reg.cxbr1_0_11.bndt = desc->transfer_len;
        if (unlikely(desc->circular_source || desc->circular_dest)) {
            /* circular mode only supported in higher channels */
            goto end;
        }
    } else {
        gpdma_register_t tr3;
        tr3.raw = 0;
        reg.cxbr1_12_15.bndt = desc->transfer_len;
        if (desc->circular_source) {
            /*
             * decrement SAR (which is incremented during burst) of the very same len (sao)
             * in order to get back to initial source address
             */
            reg.cxbr1_12_15.sdec = 1;
            tr3.cxtr3.sao = desc->transfer_len;
        }
        if (desc->circular_dest) {
            /*
             * decrement DAR (which is incremented during burst) of the very same len (sao)
             * in order to get back to initial source address
             */
            reg.cxbr1_12_15.ddec = 1;
            tr3.cxtr3.dao = desc->transfer_len;
        }
        iowrite32(ctrl_desc->base_addr + GPDMA_CxTR3(desc->channel), tr3.raw);
    }
    iowrite32(ctrl_desc->base_addr + GPDMA_CxBR1(desc->channel), reg.raw);
    /* configure source addr */
    reg.raw = 0;
    reg.cxsar.sa = desc->source;
    iowrite32(ctrl_desc->base_addr + GPDMA_CxSAR(desc->channel), reg.raw);

    reg.raw = 0;
    reg.cxdar.da = desc->dest;
    iowrite32(ctrl_desc->base_addr + GPDMA_CxDAR(desc->channel), reg.raw);

    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t stm32u5_gpdma_channel_enable(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;
    gpdma_register_t reg;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel));
    reg.cxcr.en = 1;
    iowrite32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel), reg.raw);
    gpdma_unmap();
end:
    return K_STATUS_OKAY;
}

kstatus_t stm32u5_gpdma_channel_suspend(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;
    gpdma_register_t reg;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxSR(desc->channel));
    if (reg.cxsr.idlef == 1) {
        /* stream is not started, nothing to resume */
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (reg.cxsr.suspf == 1) {
        /* stream is already suspended */
        status = K_ERROR_BADSTATE;
        goto end;
    }
    // suspend stream
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel));
    reg.cxcr.susp = 1;
    iowrite32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel), reg.raw);
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t stm32u5_gpdma_channel_resume(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;
    gpdma_register_t reg;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxSR(desc->channel));
    if (reg.cxsr.suspf == 0) {
        /* stream is not suspended */
        status = K_ERROR_BADSTATE;
        goto end;
    }
    // resume the suspended stream
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel));
    reg.cxcr.susp = 0;
    iowrite32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel), reg.raw);
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t stm32u5_gpdma_channel_reset(gpdma_stream_cfg_t const*const desc)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stm32_gpdma_desc_t const * ctrl_desc;
    gpdma_register_t reg;

    if (unlikely(desc == NULL)) {
        goto end;
    }
    ctrl_desc = stm32_gpdma_get_desc(desc->controller);
    if (unlikely(ctrl_desc == NULL)) {
        goto end;
    }
    if (unlikely(desc->channel >= ctrl_desc->num_chan)) {
        goto end;
    }
    if (unlikely(gpdma_map(desc->controller) != K_STATUS_OKAY)) {
        goto end;
    }
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxSR(desc->channel));
    if (reg.cxsr.suspf == 0) {
        /* stream is not suspended, can't be reset */
        status = K_ERROR_BADSTATE;
        goto end;
    }
    // reset channel (to be used after suspend
    reg.raw = ioread32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel));
    reg.cxcr.reset = 1;
    iowrite32(ctrl_desc->base_addr + GPDMA_CxCR(desc->channel), reg.raw);
    gpdma_unmap();
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t stm32u5_gpdma_channel_abort(void)
{
    return K_STATUS_OKAY;
}

kstatus_t stm32u5_gpdma_channel_restart(void)
{
    return K_STATUS_OKAY;
}

/* aliasing functions to generic API */
kstatus_t gpdma_probe(uint8_t controller) __attribute((alias("stm32u5_gpdma_probe")));
kstatus_t gpdma_channel_clear_status(gpdma_stream_cfg_t const*const desc) __attribute__((alias("smt32u5_gpdma_channel_clear_status")));
kstatus_t gpdma_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status) __attribute__((alias("smt32u5_gpdma_channel_get_status")));
kstatus_t gpdma_channel_configure(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32u5_gpdma_channel_configure")));
kstatus_t gpdma_channel_enable(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32u5_gpdma_channel_enable")));
kstatus_t gpdma_channel_suspend(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32u5_gpdma_channel_suspend")));
kstatus_t gpdma_channel_resume(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32u5_gpdma_channel_resume")));
kstatus_t gpdma_channel_reset(gpdma_stream_cfg_t const*const desc) __attribute__((alias("stm32u5_gpdma_channel_reset")));
kstatus_t gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn) __attribute__((alias("stm32u5_gpdma_get_interrupt")));
kstatus_t gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc) __attribute__((alias("stm32u5_gpdma_interrupt_clear")));
