// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V syscall calling convention based on Linux:
 *  https://git.kernel.org/pub/scm/docs/man-pages/man-pages.git/tree/man2/syscall.2?h=man-pages-5.04#n332
 *
 * - sycall number in a7
 * - sycall arguments in a0 to a5
 * - return value in a0
 * - return error code in a1
 */

#include <stddef.h>

#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/thread.h>
#include <sentry/arch/asm-generic/handler-svc-lut.h>

#include <sentry/managers/task.h>
#include <sentry/sched.h>
#include <sentry/syscalls.h>

//TODO: Fix uapi type include
#define STATUS_NO_ENTITY 3

static stack_frame_t *lut_send_ipc(stack_frame_t *frame) {
    taskh_t target = frame->a0;
    uint32_t len = frame->a1;
    return gate_send_ipc(frame, target, len);
}

static  stack_frame_t *lut_send_signal(stack_frame_t *frame) {
    taskh_t target = frame->a0;
    uint32_t signal = frame->a1;
    return gate_send_signal(frame, target, signal);
}

static stack_frame_t *lut_waitfoeevent(stack_frame_t *frame) {
    uint8_t event_mask = frame->a0;
    int32_t timeout = frame->a1;
    return gate_waitforevent(frame, event_mask, timeout);
}

static stack_frame_t *lut_gpio_set(stack_frame_t *frame) {
    devh_t device = frame->a0;
    uint8_t io = frame->a1;
    bool val = frame->a2;
    return gate_gpio_set(frame, device, io, val);
}

static stack_frame_t *lut_gpio_get(stack_frame_t *frame) {
    devh_t device = frame->a0;
    uint8_t io = frame->a1;
    return gate_gpio_get(frame, device, io);
}

static stack_frame_t *lut_gpio_reset(stack_frame_t *frame) {
    devh_t device = frame->a0;
    uint8_t io = frame->a1;
    return gate_gpio_reset(frame, device, io);
}

static stack_frame_t *lut_gpio_toggle(stack_frame_t *frame) {
    devh_t device = frame->a0;
    uint8_t io = frame->a1;
    return gate_gpio_toggle(frame, device, io);
}

static stack_frame_t *lut_gpio_configure(stack_frame_t *frame) {
    devh_t device = frame->a0;
    uint8_t io = frame->a1;
    return gate_gpio_configure(frame, device, io);
}

static stack_frame_t *lut_get_devhandle(stack_frame_t *frame) {
    uint8_t devid = frame->a0;
    return gate_get_devhandle(frame, devid);
}

static stack_frame_t *lut_get_shmhandle(stack_frame_t *frame) {
    uint32_t shmid = frame->a0;
    return gate_get_shmhandle(frame, shmid);
}

static stack_frame_t *lut_int_acknowledge(stack_frame_t *frame) {
    uint16_t IRQn = frame->a0;
    return gate_int_acknowledge(frame, IRQn);
}

static stack_frame_t *lut_int_enable(stack_frame_t *frame) {
    uint16_t IRQn = frame->a0;
    return gate_int_enable(frame, IRQn);
}

static stack_frame_t *lut_int_disable(stack_frame_t *frame) {
    uint16_t IRQn = frame->a0;
    return gate_int_disable(frame, IRQn);
}

static stack_frame_t *lut_map_dev(stack_frame_t *frame) {
    devh_t dev = frame->a0;
    return gate_map_dev(frame, dev);
}

static stack_frame_t *lut_unmap_dev(stack_frame_t *frame) {
    devh_t dev = frame->a0;
    return gate_unmap_dev(frame, dev);
}

static stack_frame_t *lut_exit(stack_frame_t *frame) {
    uint32_t exit_code = frame->a0;
    return gate_exit(frame, exit_code);
}

static stack_frame_t *lut_get_prochandle(stack_frame_t *frame) {
    uint32_t label = frame->a0;
    return gate_get_prochandle(frame, label);
}

static stack_frame_t *lut_get_dmahandle(stack_frame_t *frame) {
    uint32_t label = frame->a0;
    return gate_get_dmahandle(frame, label);
}

static stack_frame_t *lut_yield(stack_frame_t *frame) {
    return gate_yield(frame);
}

static stack_frame_t *lut_sleep(stack_frame_t *frame) {
    uint32_t duration_ms = frame->a0;
    uint32_t sleep_mode = frame->a1;
    return gate_sleep(frame, duration_ms, sleep_mode);
}

static stack_frame_t *lut_start(stack_frame_t *frame) {
    uint32_t target_label = frame->a0;
    return gate_start(frame, target_label);
}

static stack_frame_t *lut_get_random(stack_frame_t *frame) {
    return gate_get_random(frame);
}

static stack_frame_t *lut_pm_manage(stack_frame_t *frame) {
    uint32_t pm_cmd = frame->a0;
    return gate_pm_manage(frame, pm_cmd);
}

static stack_frame_t *lut_pm_clock_set(stack_frame_t *frame) {
    uint32_t clkreg = frame->a0;
    uint32_t clkmsk = frame->a1;
    uint32_t val = frame->a2;
    return gate_pm_clock_set(frame, clkreg, clkmsk, val);
}

static stack_frame_t *lut_alarm(stack_frame_t *frame) {
    uint32_t delay_ms = frame->a0;
    uint32_t flag = frame->a1;
    return gate_alarm(frame, delay_ms, flag);
}

static stack_frame_t *lut_get_cycle(stack_frame_t *frame) {
    uint32_t precision = frame->a0;
    return gate_get_cycle(frame, precision);
}

static stack_frame_t *lut_log(stack_frame_t *frame) {
    uint32_t len = frame->a0;
    return gate_log(frame, len);
}

static stack_frame_t *lut_map_shm(stack_frame_t *frame) {
    shmh_t shm = frame->a0;
    return gate_map_shm(frame, shm);
}

static stack_frame_t *lut_unmap_shm(stack_frame_t *frame) {
    shmh_t shm = frame->a0;
    return gate_unmap_shm(frame, shm);
}

static stack_frame_t *lut_shm_set_perms(stack_frame_t *frame) {
    shmh_t shm = frame->a0;
    taskh_t tsk = frame->a1;
    SHMPermission perms = frame->a2;
    return gate_shm_setcreds(frame, shm, tsk, perms);
}


/* For reserved yet not yet implemented syscall ids */
static stack_frame_t *lut_notsup(stack_frame_t *f) {
    mgr_task_set_sysreturn(sched_get_current(), STATUS_NO_ENTITY);
    return f;
}

static stack_frame_t *lut_shm_get_infos(stack_frame_t *frame) {
    shmh_t shm = frame->a0;
    return gate_shm_get_infos(frame, shm);
}

static stack_frame_t *lut_dma_assign(stack_frame_t *frame) {
    dmah_t dma = frame->a0;
    return gate_dma_assign(frame, dma);
}

static stack_frame_t *lut_dma_unassign(stack_frame_t *frame) {
    dmah_t dma = frame->a0;
    return gate_dma_unassign(frame, dma);
}


static stack_frame_t *lut_dma_start(stack_frame_t *frame) {
    dmah_t dma = frame->a0;
    return gate_dma_start(frame, dma);
}

static stack_frame_t *lut_dma_get_stream_info(stack_frame_t *frame) {
    dmah_t dma = frame->a0;
    return gate_dma_getinfo(frame, dma);
}

static stack_frame_t *lut_dma_stream_suspend(stack_frame_t *frame) {
    dmah_t dma = frame->a0;
    return gate_dma_suspend(frame, dma);
}

static stack_frame_t *lut_dma_stream_resume(stack_frame_t *frame) {
    dmah_t dma = frame->a0;
    return gate_dma_resume(frame, dma);
}

/* for not yet supported syscalls */
static stack_frame_t *lut_unsuported(stack_frame_t *frame) {
    mgr_task_set_sysreturn(sched_get_current(), STATUS_NO_ENTITY);
    return frame;
}

static const lut_svc_handler svc_lut[] = {
    lut_exit,
    lut_get_prochandle,
    lut_get_devhandle,
    lut_yield,
    lut_sleep,
    lut_start,
    lut_map_dev,
    lut_map_shm,
    lut_unmap_dev,
    lut_unmap_shm,
    lut_shm_set_perms,
    lut_send_ipc,
    lut_send_signal,
    lut_waitfoeevent,
    lut_pm_manage,
    lut_pm_clock_set,
    lut_log,
    lut_alarm,
    lut_get_random,
    lut_get_cycle,
    lut_gpio_get,
    lut_gpio_set,
    lut_gpio_reset,
    lut_gpio_toggle,
    lut_gpio_configure,
    lut_int_acknowledge,
    lut_int_enable,
    lut_int_disable,
    lut_get_shmhandle,
    lut_get_dmahandle,
    lut_dma_start,
    lut_dma_stream_suspend,
    lut_unsuported, /* DMA Get Stream Status */
    lut_shm_get_infos,
    lut_dma_assign,
    lut_dma_unassign,
    lut_dma_get_stream_info,
    lut_dma_stream_resume,
};


#define SYSCALL_NUM ARRAY_SIZE(svc_lut)

lut_svc_handler const *svc_lut_get(void) {
    return &svc_lut[0];
}
size_t svc_lut_size(void) {
    return SYSCALL_NUM;
}