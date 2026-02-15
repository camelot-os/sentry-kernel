// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_MANAGER_H
#define TASK_MANAGER_H

#include <assert.h>
#include <inttypes.h>
#include <stddef.h>

#include <uapi/uapi.h>
#include <uapi/handle.h>
#include <uapi/dma.h>
#include <sentry/managers/security.h>
#include <sentry/managers/device.h>
#include <sentry/managers/task_metadata.h>
#include <sentry/dma.h>
#include <sentry/ipc.h>
#include <sentry/ktypes.h>
#include <sentry/job.h>

/**
 * \file sentry kernel generic types
 */
#include <sentry/arch/asm-generic/thread.h>
#include <sentry/arch/asm-generic/memory.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @def idle task label definition
 *
 * When no task of the user task set is schedulable, the idle task is the lonely
 * task eligible. This special task is a dedicated thread that wfi() and yield()
 * so that the core can enter SLEEP mode while no interrupt rise and all tasks
 * are blocked (external event wait, sleep, etc.).
 * The idle task has a dedicated label denoted 'cafe'. This label is forbidden
 * to user tasks.
 */
#define SCHED_IDLE_TASK_LABEL 0xcafeUL

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
/**
 * @def no task label for autotest
 *
 * Autotest exists only in autotest mode, when no other task but autotest and idle
 * exist. It is used for automatic kernel testing/fuzzing, with remote control if needed
 * so that the Sentry kernel features can be properly verified.
 * See the autotest application for more information.
 */
#define SCHED_AUTOTEST_TASK_LABEL 0xbabeUL
#endif

#ifdef __FRAMAC__
/** INFO: to support fully randomized svc exchange content at anytime for Frama-C,
 * use an emulated randomized area
 */
static uint8_t svcexch[CONFIG_SVC_EXCHANGE_AREA_LEN];
#endif

/*@
    requires \valid(svcexch+(0..127));
    assigns \nothing;
    ensures \valid_read(meta) ==> (\result == &svcexch[0]);
 */
static inline uint8_t *task_get_svcexchange(const task_meta_t *meta) {
    uint8_t * exch = NULL;
    if (unlikely(meta == NULL)) {
        goto end;
    }
#ifndef __FRAMAC__
    exch = (uint8_t*)meta->s_svcexchange;
#else
    /*@ assert \valid_read(meta); */
    exch = &svcexch[0];
    /*@ assert exch == &svcexch[0]; */
#endif
end:
    return exch;
}

/*
 * About main module standardly defined functions (init, watchdog....)
 */

kstatus_t mgr_task_init(void);

void __attribute__((noreturn)) mgr_task_start(void);

kstatus_t mgr_task_watchdog(void);

/*
 * About module specific API
 */

stack_frame_t *mgr_task_initialize_sp(uint32_t rerun, size_t sp, size_t pc, size_t got);

uint32_t mgr_task_get_num(void);

kstatus_t mgr_task_get_sp(taskh_t t, stack_frame_t **sp);

kstatus_t mgr_task_get_state(taskh_t t, job_state_t *state);

kstatus_t mgr_task_get_metadata(taskh_t t, const task_meta_t **tsk_meta);

kstatus_t mgr_task_get_domain(taskh_t t, uint8_t *domain);

kstatus_t mgr_task_get_handle(uint32_t label, taskh_t *handle);

kstatus_t mgr_task_set_sp(taskh_t t, stack_frame_t *newsp);

kstatus_t mgr_task_set_state(taskh_t t, job_state_t state);

secure_bool_t mgr_task_is_idletask(taskh_t t);

secure_bool_t mgr_task_handle_exists(taskh_t t);

kstatus_t mgr_task_get_device_owner(uint16_t d, taskh_t *t);

size_t mgr_task_get_data_region_size(const task_meta_t *meta);

size_t mgr_task_get_text_region_size(const task_meta_t *meta);

secure_bool_t mgr_task_is_userspace_spawned(void);

taskh_t mgr_task_get_idle(void);

/**
 * @brief respawn a given task job
 *
 * Note that once respawned, the handle is no more valid
 * and thus accessing this task job requires a new call to sys_get_task_handle()
 */
kstatus_t task_respawn_job(taskh_t task_handle);

/**
 * @brief Add (map) a mappable resource to the task current layout
 *
 * @param t task handle
 * @param resource_id resource layout index in task layout table
 * @param resource resource to add
 */
kstatus_t mgr_task_add_resource(const taskh_t t, const uint8_t resource_id, const layout_resource_t resource);

/**
 * @brief Remove the resource identified by its id from the task current layout
 *
 * @param t task handle
 * @param resource_id resource layout index in task layout table
 */
kstatus_t mgr_task_remove_resource(taskh_t t, uint8_t resource_id);


kstatus_t mgr_task_get_layout_from_handle(taskh_t t, const layout_resource_t **layout);

/**
 * @brief get back current sysreturn value of a job
 *
 * Fails if the syscall return field is set as cleared
 */
kstatus_t mgr_task_get_sysreturn(taskh_t t, Status *sysret);

/**
 * @brief Set the currently called syscall return value of job identified by t
 *
 * Can be set synchronously by its own syscall or by another job's syscall
 */
kstatus_t mgr_task_set_sysreturn(taskh_t t, Status sysret);

/**
 * @brief clear curently set syscall return
 *
 * this will make all consecutive call to task_get_sysreturn failing
 */
kstatus_t mgr_task_clear_sysreturn(taskh_t t);

/**
 * @brief set current job return code, when leaving
 *
 * The return code of the current job aim to be used for analysis and
 * potentialy other jobs associated to it if needed.
 *
 * It also allows the usage of the restart_on_failure concept if needed
 */
kstatus_t mgr_task_set_jobreturn(taskh_t t, uint32_t returncode);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
taskh_t mgr_task_get_autotest(void);

kstatus_t mgr_task_autotest(void);
#endif

#if CONFIG_HAS_GPDMA
kstatus_t mgr_task_push_dma_event(taskh_t target, dmah_t dma_stream, gpdma_chan_state_t dma_event);
kstatus_t mgr_task_load_dma_event(taskh_t target, dmah_t *dma_stream, gpdma_chan_state_t *dma_event);
#endif

/* specialized event pushing API, do not use directly but instead Generic below */
kstatus_t mgr_task_push_int_event(uint32_t IRQn, taskh_t dest);
kstatus_t mgr_task_push_ipc_event(uint32_t len, taskh_t source, taskh_t dest);
kstatus_t mgr_task_push_sig_event(uint32_t sig, taskh_t source, taskh_t dest);

kstatus_t mgr_task_load_ipc_event(taskh_t context);
kstatus_t mgr_task_load_sig_event(taskh_t context, uint32_t *signal, taskh_t *source);
kstatus_t mgr_task_load_int_event(taskh_t context, uint32_t *IRQn);

/* get back peer that has emitted IPC to owner, in iterative way
 * if status = K_STATUS_NOENT, no more IPC, if status = OKAY, peer hold the emitter handle
 * idx is incremented as an opaque, to continue checking.
 */
kstatus_t mgr_task_local_ipc_iterate(taskh_t owner, taskh_t *peer, uint8_t *idx);

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
