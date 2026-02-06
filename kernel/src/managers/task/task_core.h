// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_CORE_H
#define TASK_CORE_H

/**
 * @file task core functions private API for task manager internal
 */

#include <uapi/uapi.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/memory.h>

#define TASK_EVENT_QUEUE_DEPTH 16

#define HANDLE_TASKID 0x0UL

typedef struct __attribute__((packed)) ktaskh  {
    uint32_t rerun : 20;
    uint32_t id : 8;
    uint32_t family : 3;
} ktaskh_t;

static_assert(sizeof(ktaskh_t) == sizeof(taskh_t), "taskh_t opaque model failure!");

/*@
    requires \valid_read(th);
    assigns \nothing;
*/
static inline const ktaskh_t * taskh_to_ktaskh(const taskh_t * th) {
    /*@ assert \valid_read(th); */
    /*
     * Note: here, ktaskh_t and taskht_t have the very same size (demonstrated using
     * the static_assert above.
     * Moreover, taskh_t is a uint32_t opaque type, and ktaskh_t is a packed struct with
     * bitfield, but the bitfield layout is designed to fit in a uint32_t,
     * so the memory layout of both types is compatible.
     * Here, we ask gcc to gently not complain about the address of packed member,
     * as we are sure that the layout is compatible and that this is a safe operation.
     */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Waddress-of-packed-member"
    return (const ktaskh_t *)th;
#pragma GCC diagnostic pop
}

/*@
    requires \valid_read(kth);
    assigns \nothing;
*/
static inline const taskh_t * ktaskh_to_taskh(const ktaskh_t * kth) {
    /*@ assert \valid_read(kth); */
    /*
     * Note: here, ktaskh_t and taskht_t have the very same size (demonstrated using
     * the static_assert above.
     * Moreover, taskh_t is a uint32_t opaque type, and ktaskh_t is a packed struct with
     * bitfield, but the bitfield layout is designed to fit in a uint32_t,
     * so the memory layout of both types is compatible.
     * Here, we ask gcc to gently not complain about the address of packed member,
     * as we are sure that the layout is compatible and that this is a safe operation.
     */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Waddress-of-packed-member"
    return (const taskh_t *)kth;
#pragma GCC diagnostic pop
}

#if CONFIG_HAS_GPDMA
/** @struct queue of GPDMA input events
 *
 * @note the event field, being an enumerate, is kept fixed u32 size to avoid
 * any compiler-specific size variation, keeping 64b size length whatever the
 * compiler is.
 */
typedef struct tsk_gpdma_event_queue {
    dmah_t      handle; /**< DMA stream handle associated to the event */
    uint32_t    event;  /**< DMA event to be pushed back to the userspace */
} tsk_gpdma_event_queue_t;
static_assert(sizeof(tsk_gpdma_event_queue_t) == sizeof(uint64_t), "invalid structure size");
#endif

typedef struct  task {
    /* about task layouting */
    /** a task hold at most TASK_MAX_RESSOURCES_NUM regions (see memory.h backend)
       CAUTION: this field is size-impacting in kernel RAM !
    */
    layout_resource_t layout[TASK_MAX_RESSOURCES_NUM];
    uint32_t num_ressources; /* number of ressources, including txt and data */
    const task_meta_t *metadata; /**< task metadata (const, build-time, informations) */
    /*
     * Task context information, these fields store dynamic values, such as current
     * task frame, current received ipc or signal events from others, etc.
     * Only fully sched-relative infos (current quantum) are not stored in the task
     * structure but directly in the scheduler context, when the scheduler do support
     * such model (quantum-based).
     */

    ktaskh_t        handle;     /**< current job handle (with rerun updated) */
    stack_frame_t   *sp;        /**< current process lonely thread stack context */

    /* about events */

    /**
      Each task only has one IPC context (only blocking IPC supported).
      When sending IPC, the thread is preempted and wait for the other
      to read for its IPC content (no double user/kernel copy, only
      user-to-user blob) ensured by disabled reentrancy in kernel.
      The context hold only, for a given task, the info indicating if
      there is an IPC received and its effective size.
      When impacting the thread state (blocking IPC, the state falg
      is used)
    */
    uint32_t           ipcs[CONFIG_MAX_TASKS];       /**< List of IPCs event (one per peer task) */
    uint32_t           sigs[CONFIG_MAX_TASKS];       /**< List of SIGs event (one per peer task) */
    uint32_t           ints[TASK_EVENT_QUEUE_DEPTH]; /**< List of IRQ events */
#if CONFIG_HAS_GPDMA
    tsk_gpdma_event_queue_t  dmas[TASK_EVENT_QUEUE_DEPTH]; /**< List of DMA events */
    uint8_t            dmas_head;
    uint8_t            dmas_bottom;
#endif
    uint8_t            ints_head;
    uint8_t            ints_bottom;

    job_state_t     state;      /**< current task state */
    uint32_t        returncode;  /**< current task job return value, when exiting */
    secure_bool_t   sysretassigned; /**< a syscall has assigned a sysreturn */
    Status          sysreturn;  /**< current job syscall return */
} task_t;


kstatus_t task_set_job_layout(task_t * const tsk);

task_t *task_get_table(void);

task_t *task_get_from_handle(taskh_t h);

void task_dump_table(void);

#endif/*!TASK_INIT_H*/
