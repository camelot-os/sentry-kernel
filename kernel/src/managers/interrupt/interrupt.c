// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi/handle.h>
#include <sentry/managers/clock.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/thread.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/device.h>
#include <sentry/managers/dma.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/sched.h>

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/clk/pwr.h>
#include <bsp/drivers/flash/flash.h>
#include <bsp/drivers/dma/gpdma.h>

/**
 * @brief push IRQn to owner's input queue, and schedule it if all hypothesis are valid
 *
 * This function is agnostic of the IRQn properties (DMA IRQ, shared IRQ, etc.) and
 * only push the IRQ to the target task input IRQ FIFO.
 */
static inline void int_push_and_schedule(taskh_t owner, int IRQn)
{
    job_state_t owner_state;

    if (unlikely(mgr_task_get_state(owner, &owner_state) != K_STATUS_OKAY)) {
       panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* push the inth event into the task input events queue */
    if (unlikely(mgr_task_push_int_event(IRQn, owner) != K_STATUS_OKAY)) {
        /* failed to push IRQ event !!! XXX: what do we do ? */
        panic(PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG);
    }
    if ((owner_state == JOB_STATE_SLEEPING) ||
        (owner_state == JOB_STATE_WAITFOREVENT)) {
        /* if the job exists in the delay queue (sleep or waitforevent with timeout)
         * remove it from the delay queue before schedule
         * TODO: use a dedicated state (WAITFOREVENT_TIMEOUT) to call this
         * function only if needed
         */
        mgr_time_delay_del_job(owner);
        mgr_task_set_sysreturn(owner, STATUS_INTR);
        mgr_task_set_state(owner, JOB_STATE_READY);
        sched_schedule(owner);
    }
}

static inline stack_frame_t *devisr_handler(stack_frame_t *frame, int IRQn)
{
    devh_t dev;
    taskh_t owner;

    /* get the device owning the interrupt */
    if (unlikely(mgr_device_get_devh_from_interrupt(IRQn, &dev) != K_STATUS_OKAY)) {
        /* interrupt with no known device ???? */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* get the task owning the device */
    if (unlikely(mgr_device_get_owner(dev, &owner) != K_STATUS_OKAY)) {
        /* user interrupt with no owning task ???? */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* masking interrupt, let the userspace unmask at its handler level */
    interrupt_disable_irq(IRQn);
    int_push_and_schedule(owner, IRQn);

    /** NOTE: we do not elect here, meaning that if the owner is not the current task, it
     * it do not synchronously preempt the task, but instead let the quantum management
     * execute the election. This generates potential latency
     */
    return frame;
}

#if CONFIG_HAS_GPDMA
/**
 * @brief push DMA vent to owner's input queue, and schedule it if all hypothesis are valid
 *
 * This function is agnostic of the DMA vent properties only push the event to the target task input FIFO.
 */
static inline void dma_push_and_schedule(taskh_t owner, dmah_t handle, gpdma_chan_state_t event)
{
    job_state_t owner_state;

    if (unlikely(mgr_task_get_state(owner, &owner_state) != K_STATUS_OKAY)) {
       panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* push the inth event into the task input events queue */
    if (unlikely(mgr_task_push_dma_event(owner, handle, event) != K_STATUS_OKAY)) {
        /* failed to push IRQ event !!! XXX: what do we do ? */
        panic(PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG);
    }
    if ((owner_state == JOB_STATE_SLEEPING) ||
        (owner_state == JOB_STATE_WAITFOREVENT)) {
        /* if the job exists in the delay queue (sleep or waitforevent with timeout)
         * remove it from the delay queue before schedule
         * TODO: use a dedicated state (WAITFOREVENT_TIMEOUT) to call this
         * function only if needed
         */
        mgr_time_delay_del_job(owner);
        mgr_task_set_sysreturn(owner, STATUS_INTR);
        mgr_task_set_state(owner, JOB_STATE_READY);
        sched_schedule(owner);
    }
}

static inline stack_frame_t *dmaisr_handler(stack_frame_t *frame, int IRQn)
{
    dmah_t dma;
    taskh_t owner = 0;
    gpdma_chan_state_t event;
    gpdma_stream_cfg_t const * cfg;

    /* get the dmah owning the interrupt */
    if (unlikely(mgr_dma_get_dmah_from_interrupt(IRQn, &dma) != K_STATUS_OKAY)) {
        /* interrupt with no known stream ???? */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* get the task owning the device */
    if (unlikely(mgr_dma_get_owner(dma, &owner) != K_STATUS_OKAY)) {
        /* user interrupt with no owning task ???? */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* inform DMA manager of DMA event, in order to handle state and status */
    if (unlikely(mgr_dma_treat_chan_event(dma) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_dma_get_status(dma, &event) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }

    /** TODO: call DMA driver for GPDMA-related interrupt acknowledge first */
    /**
     * NOTE: no need to check for this API return code, as this function panic() on failure.
     * Although, to avoid inter-managers implementation dependencies, we duplicate the return
     * check here, as a unlikely, never callable block (dead-code)
    */
    dma_push_and_schedule(owner, dma, event);
    if (unlikely(mgr_dma_get_info(dma, &cfg) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /*@ assert \valid_read(cfg); */
    /* Clearing interrupt at DMA and NVIC level */
    if (unlikely(gpdma_interrupt_clear(cfg) != K_STATUS_OKAY)) {
        panic(PANIC_HARDWARE_INVALID_STATE);
    }
    interrupt_clear_pendingirq(IRQn);
    return frame;
}
#endif

stack_frame_t *userisr_handler(stack_frame_t *frame, int IRQn)
{
    /* differentiate DMA IRQ from devices IRQ
     * DMA IRQn are associated to dma handles (bijection with a dts stream),
     * while user devices IRQn are associated to dev handle (bijection with a device)
     */
#if CONFIG_HAS_GPDMA
    if (gpdma_irq_is_dma_owned(IRQn)) {
        frame = dmaisr_handler(frame, IRQn);
        goto end;
    }
#endif
    frame = devisr_handler(frame, IRQn);
#if CONFIG_HAS_GPDMA
end:
#endif
    return frame;
}

kstatus_t mgr_interrupt_init(void)
{
    /** FIXME: implement init part of interrupt manager */
    interrupt_init(); /** still needed again ? */
    return K_STATUS_OKAY;
}

/**
 * @brief enable IRQ line associated to given IRQ number
 *
 * @param[in] irq IRQ number to enable
 *
 * @return K_ERROR_INVPARAM if irq is invalid on the platform, or K_STATUS_OKAY
 */
kstatus_t mgr_interrupt_enable_irq(uint32_t irq)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(irq >= NUM_IRQS)) {
        goto err;
    }
    interrupt_enable_irq(irq);
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief disable IRQ line associated to given IRQ number
 *
 * @param[in] irq IRQ number to disable
 *
 * @return K_ERROR_INVPARAM if irq is invalid on the platform, or K_STATUS_OKAY
 */
kstatus_t mgr_interrupt_disable_irq(uint32_t irq)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(irq >= NUM_IRQS)) {
        goto err;
    }
    interrupt_disable_irq(irq);
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_interrupt_acknowledge_irq(int IRQn)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(interrupt_clear_pendingirq(IRQn)!= K_STATUS_OKAY)) {
        goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_interrupt_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

/** FIXME: add interrupt manipulation (add user handler, del user handler, etc.) */
