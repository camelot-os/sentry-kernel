// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/managers/task.h>
#include <sentry/managers/dma.h>
#include <sentry/managers/security.h>
#include <sentry/managers/interrupt.h>
#include <sentry/arch/asm-generic/panic.h>
#include <bsp/drivers/dma/gpdma.h>
#include "dma-dt.h"
#include "dma.h"

static dma_stream_config_t stream_config[STREAM_LIST_SIZE];

#ifndef CONFIG_HAS_GPDMA
static_assert(STREAM_LIST_SIZE, "Can't have streams when no GPDMA supported!");
#endif

kstatus_t mgr_dma_init(void)
{
    kstatus_t status = K_STATUS_OKAY;

#if STREAM_LIST_SIZE
    for (size_t streamid = 0; streamid < STREAM_LIST_SIZE; ++streamid) {
        kdmah_t kdmah = {
            .reserved = 0,
            .family = HANDLE_DMA,
            .streamid = streamid,
        };
        uint32_t seed = 0;

        /* Add entropy to handle initialization */
        if (unlikely(mgr_security_entropy_generate(&seed) != K_STATUS_OKAY)) {
            panic(PANIC_HARDWARE_INVALID_STATE);
            __builtin_unreachable();
        }
        kdmah.reserved = seed;

        dmah_t const *dmah = kdmah_to_dmah(&kdmah);
        if (unlikely(dma_stream_get_meta(streamid, &stream_config[streamid].meta) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
            __builtin_unreachable();

        }
        if (unlikely(mgr_task_get_handle(stream_config[streamid].meta->owner, &stream_config[streamid].owner) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
            __builtin_unreachable();
        }

        /*@ assert \valid(dmah); */
        /*@ assert \valid_read(stream_config[streamid].meta); */
        stream_config[streamid].handle = *dmah;
        stream_config[streamid].state = DMA_STREAM_STATE_UNSET; /** FIXME: define status types for streams */
        stream_config[streamid].status.completed = 0;
        stream_config[streamid].status.half_reached = 0;
        stream_config[streamid].status.state = GPDMA_STATE_IDLE;
        /*
         * FIXME:
         * by now, here we have a naive probbing mechanism, meaning that
         * we probe for each stream we have, and thus may probe multiple
         * time the same IP.
         * This should not have impact but this is not a good methodology.
         */
        if (unlikely(gpdma_probe(stream_config[streamid].meta->config.controller) != K_STATUS_OKAY)) {
            status = K_ERROR_BADSTATE;
            goto end;
        };
    }
end:
#endif
    return status;
}

/**
 * @fn mgr_dma_get_config - returns the configuration associated to given handle
 *
 * @param[in] dmah: DMA handle for which the config is asked
 *
 * @returns: DMA configuration if found, or NULL
 */
static dma_stream_config_t *mgr_dma_get_config(const dmah_t dmah)
{
    dma_stream_config_t * cfg = NULL;
#if STREAM_LIST_SIZE
    for (size_t streamid = 0; streamid < STREAM_LIST_SIZE; ++streamid) {
        if (stream_config[streamid].handle == dmah) {
            cfg = &stream_config[streamid];
            goto end;
        }
    }
end:
#endif
    return cfg;
}

/**
 * @fn get static metainformation about a DMA stream identified by its handle
 *
 * The static metainformation is the overall stream definition as declared in the
 * device tree. The corresponding kernel structure (const build time forged) is
 * returned.
 *
 * @param[in] dmah: DMA stream handle for which the data is requested
 * @param[out] infos: DMA stream info address to be updated
 *
 * @return K_STATUS_OKAY if successfully found and updated, or K_ERROR_INVPARAM.
 */
kstatus_t mgr_dma_get_info(const dmah_t dmah, gpdma_stream_cfg_t const ** infos)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(infos == NULL)) {
        goto end;
    }
#if STREAM_LIST_SIZE
    for (size_t streamid = 0; streamid < STREAM_LIST_SIZE; ++streamid) {
        if (stream_config[streamid].handle == dmah) {
            *infos = &stream_config[streamid].meta->config;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
#endif
end:
    return status;
}

kstatus_t mgr_dma_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

/**
 * @fn mgr_dma_get_handle - get back DMA handle from given DMA label
 *
 * @param label[in]: DMA label as defined in the DTS and known by the ownering task
 * @param handle[out]: DMA handle associated to the DMA label
 *
 * @returns:
 *  K_ERROR_INVPARAM: label is invalid or handle is not a valid rw-pointer
 *  K_STATUS_OKAY: handle found and assigned to handle parameter
 */
kstatus_t mgr_dma_get_handle(const uint32_t label, dmah_t * handle)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(handle == NULL)) {
        goto end;
    }

#if STREAM_LIST_SIZE
    for (size_t streamid = 0; streamid < STREAM_LIST_SIZE; ++streamid) {
        /*@ assert \valid_read(stream_config[streamid].meta); */
        if (stream_config[streamid].meta->label == label) {
            *handle = stream_config[streamid].handle;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
#endif
end:
    return status;
}

/**
 * @brief given a DMA stream handle, return the task handle associated to it
 *
 * @param[in] dmah: DMA handle for which the owner is asked
 * @param[out] owner: Owner of the DMA handle, if found

 *
 * @return
 *   K_ERROR_INVPARAM: handle does not exist or owner is not valid
 *   K_STATUS_OKAY: owner found and owner argument updated
 */
kstatus_t mgr_dma_get_owner(dmah_t d, taskh_t *owner)
{
    kstatus_t status = K_ERROR_INVPARAM;
#if STREAM_LIST_SIZE == 0
    goto end;
#else
    uint32_t owner_label;
    if (unlikely(owner == NULL)) {
        goto end;
    }
    kdmah_t const *kdmah = dmah_to_kdmah(&d);
    if (kdmah->streamid >= STREAM_LIST_SIZE) {
        goto end;
    }
    if (stream_config[kdmah->streamid].handle != d) {
        goto end;
    }
    *owner = stream_config[kdmah->streamid].owner;
    status = K_STATUS_OKAY;
#endif
end:
    return status;
}

kstatus_t mgr_dma_treat_chan_event(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    dma_stream_config_t * const cfg = mgr_dma_get_config(dmah);
    gpdma_chan_status_t dma_status;

    if (unlikely(cfg == NULL)) {
        goto end;
    }

    /* an interrupt has risen, get back stream HW status from GPDMA upper API */
    if (unlikely(gpdma_channel_get_status(&cfg->meta->config, &cfg->status) != K_STATUS_OKAY)) {
        goto end;
    }
    /* react on interrupt: update state automaton */
    if (cfg->status.completed && cfg->status.state == GPDMA_STATE_IDLE) {
        cfg->state = DMA_STREAM_STATE_ASSIGNED;
    }
    if (cfg->status.state == GPDMA_STATE_SUSPENDED) {
        cfg->state = DMA_STREAM_STATE_SUSPENDED;
    }
    /* clearing status no that IT-related status has been stored in the stream status field */
    gpdma_channel_clear_status(&cfg->meta->config);
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_dma_get_status(dmah_t d, gpdma_chan_state_t *dma_status)
{
    kstatus_t status;
    /*@ assert \valid(dma_status); */
#if STREAM_LIST_SIZE == 0
    status = K_ERROR_NOENT;
    goto end;
#else
    status = K_ERROR_INVPARAM;
    kdmah_t const *kdmah = dmah_to_kdmah(&d);

    if (unlikely(dma_status == NULL)) {
        goto end;
    }
    if (kdmah->streamid >= STREAM_LIST_SIZE) {
        goto end;
    }
    if (stream_config[kdmah->streamid].handle != d) {
        goto end;
    }
    *dma_status = stream_config[kdmah->streamid].status.state;
    status = K_STATUS_OKAY;
#endif
end:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_dma_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

/**
 * @brief given an IRQ number, return the started stream's handle associated to it
 *
 * This concept requires that each DMA controler's channel is linked to a single handle at a given time
 *
 * @param[in] IRQn: IRQ number received from the core (nvic, etc.) IRQ controller
 * @param[out] dmah: DMA handle that is associated to that IRQ
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not a valid pointer
 *   K_STATUS_OKAY: stream assignation done with success
 */
kstatus_t mgr_dma_get_dmah_from_interrupt(const uint16_t IRQn, dmah_t *dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint16_t stream_irqn = 0;
    uint16_t stream;
    gpdma_stream_cfg_t const *cfg = NULL;

    if (unlikely(dmah == NULL)) {
        goto end;
    }
#if STREAM_LIST_SIZE
    /* 1. get back dma {chan,ctrl} couple from IRQn */
    for (stream = 0; stream < STREAM_LIST_SIZE; ++stream) {
        cfg = &stream_config[stream].meta->config;
        /* stream hold the ctrl/chan couple from which we can deduce the IRQn */
        /*@ assert \valid_read(cfg); */
        if (unlikely(gpdma_get_interrupt(cfg, &stream_irqn) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
            __builtin_unreachable();
        }
        if (stream_irqn == IRQn) {
            *dmah = stream_config[stream].handle;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    /* not found, leaving with error */
    status = K_ERROR_NOENT;
    goto end;
#endif
end:
    return status;
}

/**
 * @brief assign a DMA stream configuration associated to given handle to the DMA controller channel
 *
 * The DMA stream is not started, but only assigned. The stream can be started either by a
 * hardware IP configured in DMA mode in case of DEVICE_TO_MEMORY mode, or by a call to the DMA
 * stream start syscall.
 *
 * @param[in] dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is already assigned/started
 *   K_STATUS_OKAY: stream assignation done with success
 */
kstatus_t mgr_dma_stream_assign(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    dma_stream_config_t * const cfg = mgr_dma_get_config(dmah);
    uint16_t IRQn;

    if (unlikely(cfg == NULL)) {
        goto end;
    }
    /* can't assign a stream that is already assigned. unassign first */
    if (unlikely(cfg->state != DMA_STREAM_STATE_UNSET)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely((status = gpdma_channel_configure(&cfg->meta->config)) != K_STATUS_OKAY)) {
        goto end;
    }
    cfg->state = DMA_STREAM_STATE_ASSIGNED;
    gpdma_get_interrupt(&cfg->meta->config, &IRQn);
    mgr_interrupt_enable_irq(IRQn);
end:
    return status;
}

/**
 * @brief unassign a DMA stream configuration associated to given handle from the DMA controller channel
 *
 * The DMA stream is unassigned, the channel is reconfigured to its reset time value.
 *
 * @param[in] dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is not assigned or is currently started
 *   K_STATUS_OKAY: stream assignation done with success
 */
kstatus_t mgr_dma_stream_unassign(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    dma_stream_config_t * const cfg = mgr_dma_get_config(dmah);

    if (unlikely(cfg == NULL)) {
        goto end;
    }
    /* can't unassign a stream that is started or already unassigned */
    if (unlikely(
          (cfg->state != DMA_STREAM_STATE_ASSIGNED) &&
          (cfg->state != DMA_STREAM_STATE_SUSPENDED)
        )) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    /* unassigning a suspended stream requires to reset first */
    if (cfg->state == DMA_STREAM_STATE_SUSPENDED) {
        if (unlikely(gpdma_channel_reset(&cfg->meta->config) != K_STATUS_OKAY)) {
            status = K_ERROR_BADSTATE;
            goto end;
        }
    }
    cfg->state = DMA_STREAM_STATE_UNSET;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief update DMA stream dynamic fields
 *
 * @param[in] dmah: DMA stream handle to set
 * @param[in] src_offset: offset (in bytes) starting from source address of DTS stream
 * @param[in] dest_offset: offset (in bytes) starting from destination address of DTS stream
 *
 * @return
 *   K_STATUS_OKAY: offsets are updated. The stream must not be started. If assigned, the channel configuration is updated
 *   K_ERROR_INVPARAM: one of the parameters is invalid
 *   K_ERROR_BADSTATE: stream is started and can't be dynamically updated now.
 */
kstatus_t mgr_dma_update_streamcfg(const dmah_t dmah, size_t src_offset, size_t dest_offset)
{
    kstatus_t status = K_ERROR_INVPARAM;
    return status;
}

/**
 * @brief start a previously assigned DMA stream associated to given handle
 *
 * The DMA stream is started. It is considered that it has been previously assigned.
 *
 * @param[in] dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is already started or has not been assigned
 *   K_STATUS_OKAY: stream has been started
 */
kstatus_t mgr_dma_stream_start(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    dma_stream_config_t * const cfg = mgr_dma_get_config(dmah);

    if (unlikely(cfg == NULL)) {
        goto end;
    }
    /* config entry, when found, must have its meta field properly set (dma_init time set) */
    /*@ assert \valid_read(cfg); */
    /*@ assert \valid_read(cfg->meta); */

    /* can't unassign a stream that is started or already unassigned */
    if (unlikely(
          (cfg->state != DMA_STREAM_STATE_ASSIGNED) &&
          (cfg->state != DMA_STREAM_STATE_SUSPENDED)
        )) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    status = gpdma_channel_enable(&cfg->meta->config);
    cfg->state = DMA_STREAM_STATE_STARTED;
    /* returns the status code returned by driver start API*/
end:
    return status;

}

/**
 * @brief suspend an already started DMA stream identified by dmah
 *
 * @param[in]: dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is not started
 *   K_STATUS_OKAY: stream has been stopped
 */
kstatus_t mgr_dma_stream_suspend(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    dma_stream_config_t * const cfg = mgr_dma_get_config(dmah);

    if (unlikely(cfg == NULL)) {
        goto end;
    }
    /* config entry, when found, must have its meta field properly set (dma_init time set) */
    /*@ assert \valid_read(cfg); */
    /*@ assert \valid_read(cfg->meta); */

    /* can't unassign a stream that is started or already unassigned */
    if (unlikely(cfg->state != DMA_STREAM_STATE_STARTED)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    status = gpdma_channel_suspend(&cfg->meta->config);
    if (likely(status == K_STATUS_OKAY)) {
        cfg->state = DMA_STREAM_STATE_SUSPENDED;
    }
    /* returns the status code returned by driver start API*/
end:
    return status;
}

/**
 * @brief resume an already started DMA stream identified by dmah
 *
 * @param[in]: dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is not suspended
 *   K_STATUS_OKAY: stream has been resumed properly
 */
kstatus_t mgr_dma_stream_resume(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    dma_stream_config_t * const cfg = mgr_dma_get_config(dmah);

    if (unlikely(cfg == NULL)) {
        goto end;
    }
    /* config entry, when found, must have its meta field properly set (dma_init time set) */
    /*@ assert \valid_read(cfg); */
    /*@ assert \valid_read(cfg->meta); */

    /* can't unassign a stream that is started or already unassigned */
    if (unlikely(cfg->state != DMA_STREAM_STATE_SUSPENDED)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    status = gpdma_channel_resume(&cfg->meta->config);
    if (likely(status == K_STATUS_OKAY)) {
        cfg->state = DMA_STREAM_STATE_STARTED;
    }
    /* returns the status code returned by driver start API*/
end:
    return status;
}
