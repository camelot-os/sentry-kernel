// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/sched.h>
#include <uapi/types.h>
#include <uapi/dma.h>
#include <sentry/arch/asm-generic/panic.h>


static inline void gate_waitforevent_populate_dma(taskh_t current, dmah_t dma, gpdma_chan_state_t event)
{
    task_meta_t const *meta;
    uint8_t *svc;
    exchange_event_t *dest_svcexch;
    /* forge SVC exchange with received signal informations */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        /* this should never happen !*/
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        __builtin_unreachable();
    }
    /*@ assert \valid_read(meta); */
    svc = task_get_svcexchange(meta);
    /*@ assert \valid(svc); */
    dest_svcexch = (exchange_event_t*)svc;
    /* set T,L values from TLV */
    dest_svcexch->type = EVENT_TYPE_DMA;
    dest_svcexch->length = sizeof(uint8_t);
    dest_svcexch->magic = 0x4242; /** FIXME: define a magic shared with uapi */
    dest_svcexch->source = dma; /**< stream source of event */
    /* here, event is encoded on 8bits length */
    dest_svcexch->data[0] = event;
}

/**
 * @fn gate_waitforevent_populate_signal : populate svc exchange with signal info
 */
static inline void gate_waitforevent_populate_signal(taskh_t current, uint8_t sig, taskh_t source)
{
    task_meta_t const *meta;
    uint8_t *svc;
    exchange_event_t *dest_svcexch;
    /* forge SVC exchange with received signal informations */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        /* this should never happen !*/
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        __builtin_unreachable();
    }
    /*@ assert \valid_read(meta); */
    svc = task_get_svcexchange(meta);
    /*@ assert \valid(svc); */
    dest_svcexch = (exchange_event_t*)svc;
    /* set T,L values from TLV */
    dest_svcexch->type = EVENT_TYPE_SIGNAL;
    dest_svcexch->length = sizeof(uint32_t);
    dest_svcexch->magic = 0x4242; /** FIXME: define a magic shared with uapi */
    dest_svcexch->source = source;
    uint32_t *sigdata = (uint32_t*)&dest_svcexch->data;
    sigdata[0] = sig;

}

/**
 * @fn gate_waitforevent_populate_interrupt : populate svc exchange with interrupt info
 */
static inline void gate_waitforevent_populate_interrupt(taskh_t current, uint32_t irq, devh_t source)
{
    task_meta_t const *meta;
    uint8_t *svc;
    exchange_event_t *dest_svcexch;
    /* forge SVC exchange with received signal informations */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        /* this should never happen !*/
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        __builtin_unreachable();
    }
    /*@ assert \valid_read(meta); */
    svc = task_get_svcexchange(meta);
    /*@ assert \valid(svc); */
    dest_svcexch = (exchange_event_t*)svc;
    /* set T,L values from TLV */
    dest_svcexch->type = EVENT_TYPE_IRQ;
    dest_svcexch->length = sizeof(uint32_t);
    dest_svcexch->magic = 0x4242; /** FIXME: define a magic shared with uapi */
    dest_svcexch->source = source;
    uint32_t *sigdata = (uint32_t*)&dest_svcexch->data;
    sigdata[0] = irq;

}

stack_frame_t *gate_waitforevent(stack_frame_t *frame,
                               uint8_t          mask,
                               int32_t          timeout)

{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = frame;
    /* ordered check of events, starting with signal... */
    if (mask & EVENT_TYPE_SIGNAL) {
        uint32_t sig;
        taskh_t source;
        if (mgr_task_load_sig_event(current, &sig, &source) == K_STATUS_OKAY) {
            gate_waitforevent_populate_signal(current, sig, source),
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
    /* and then irq... */
    if (mask & EVENT_TYPE_IRQ) {
        uint32_t irqn;
        devh_t devh;
        if (mgr_task_load_int_event(current, &irqn) == K_STATUS_OKAY) {
            mgr_device_get_devh_from_interrupt(irqn, &devh);
            gate_waitforevent_populate_interrupt(current, irqn, devh);
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
#if CONFIG_HAS_GPDMA
    if (mask & EVENT_TYPE_DMA) {
        dmah_t dmah;
        gpdma_chan_state_t event;
        if (mgr_task_load_dma_event(current, &dmah, &event) == K_STATUS_OKAY) {
            gate_waitforevent_populate_dma(current, dmah, event);
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
#endif
    /* and then ipc... */
    if (mask & EVENT_TYPE_IPC) {
        if (mgr_task_load_ipc_event(current) == K_STATUS_OKAY) {
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
    if (timeout == -1) {
        /* do not deschedule the job */
        mgr_task_set_sysreturn(current, STATUS_AGAIN);
        goto end;
    }
    if (timeout > 0) {
        mgr_time_delay_add_job(current, timeout);
    }
    /* no event at all... delaying if timeout, and schedule */
    mgr_task_set_state(current, JOB_STATE_WAITFOREVENT);
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
    next = sched_elect();
    mgr_task_get_sp(next, &next_frame);
end:
    return next_frame;
}
