// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager core functions
 */

#include <inttypes.h>
#include <assert.h>
#include <string.h>
#include <limits.h>
#include <uapi/types.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/memory.h>
#include <sentry/zlib/math.h>
#include <sentry/sched.h>
#include "task_init.h"
#include "task_idle.h"
#include "task_core.h"


#ifndef TEST_MODE

/* idle task position, from linker script */
extern size_t _idle;
#endif


/**
 * @def table of tasks, polulated at boot time during metadata analysis
 *
 * contains all dynamic content of tasks (current sp, state...)
 * This table is sorted based on the task label (taskh_t id field) for binary search.
 * task metadata table may not.
 * This table also hold the IDLE task context, which is not a task that has been forged from
 * the upper metadata info but is a kernel local unprivilegied thread, yet holding a
 * specific task handle (i.e. with 0xCAFE mabel). Idle task has no metadata as it doesn't
 * hold any ressource (dev, shm, dma...), any capability, neither heap content or nothing,
 * but instead just do { while(1) { wfi(); yield(); }}.
 * INFO: zeroified as in .bss.
 */
#ifndef TEST_MODE
/* in test mode, we get back the table for analysis */
static
#endif
_Alignas(uint64_t) task_t task_table[CONFIG_MAX_TASKS+1];

/**
 * @brief return the local task table address
 *
 * for local manager's purpose only, exported through local header exclusively
 */
task_t *task_get_table(void)
{
    return &task_table[0];
}

/**
 * TODO: this calculation may be done once for a task at boot time and stord
 * in task dyn data. This though required a fast taskh to task info accessor
 */
size_t mgr_task_get_data_region_size(const task_meta_t *meta)
{
    /*@ assert \valid_read(meta); */
    return CONFIG_SVC_EXCHANGE_AREA_LEN + \
           ROUND_UP(meta->got_size, __WORDSIZE) + \
           ROUND_UP(meta->data_size, __WORDSIZE) + \
           ROUND_UP(meta->bss_size, __WORDSIZE) + \
           ROUND_UP(meta->heap_size, __WORDSIZE) + \
           ROUND_UP(meta->stack_size, __WORDSIZE);
}

/**
 * TODO: this calculation may be done once for a task at boot time and stord
 * in task dyn data. This though required a fast taskh to task info accessor
 */
size_t mgr_task_get_text_region_size(const task_meta_t *meta)
{
    /*@ assert \valid_read(meta); */
    return ROUND_UP(meta->text_size, __WORDSIZE) + \
           meta->rodata_size;
    /* got and data in flash are excluded (no need) */
}

void task_dump_table(void)
{
#ifndef CONFIG_BUILD_TARGET_RELEASE
    /* dump all tasks including idle */
    for (uint8_t i = 0; i < mgr_task_get_num(); ++i) {
        task_t *t = &task_table[i];
        uint32_t label = t->metadata->label;
        pr_debug("=== Task labeled '%lx' metainformations:", label);
        pr_debug("[%02x] --- scheduling and permissions", label);
        pr_debug("[%02x] task priority:\t\t\t%u", label, t->metadata->priority);
        pr_debug("[%02x] task quantum:\t\t\t%u", label, t->metadata->quantum);
        pr_debug("[%02x] task capabilities:\t\t\t%08x", label, t->metadata->capabilities);
        pr_debug("[%02x] task handle value:\t\t\t%08x", label, t->handle);
        pr_debug("[%02x] --- mapping", label);
        pr_debug("[%02x] task svc_exchange section start:\t%p", label, t->metadata->s_svcexchange);
        pr_debug("[%02x] task text section start:\t\t%p", label, t->metadata->s_text);
        pr_debug("[%02x] task text section size:\t\t%u", label, t->metadata->text_size);
        pr_debug("[%02x] task rodata section size:\t\t%u", label, t->metadata->rodata_size);
        pr_debug("[%02x] task data section size:\t\t%u", label, t->metadata->data_size);
        pr_debug("[%02x] task bss section size:\t\t%u", label, t->metadata->bss_size);
        pr_debug("[%02x] task stack size:\t\t\t%u", label, t->metadata->stack_size);
        pr_debug("[%02x] task heap size:\t\t\t%u", label, t->metadata->heap_size);
        pr_debug("[%02x] task _start offset from text base:\t%u", label, t->metadata->entrypoint_offset);
    }
#endif
}

secure_bool_t mgr_task_handle_exists(taskh_t h)
{
    secure_bool_t res = SECURE_FALSE;
    if (unlikely(task_get_from_handle(h) == NULL)) {
        goto end;
    }
    res = SECURE_TRUE;
end:
    return res;
}

task_t *task_get_from_handle(taskh_t h)
{
    task_t *tsk = NULL;
    const taskh_t *cell_handle;
    const ktaskh_t *kh = taskh_to_ktaskh(&h);
    /* check that handle identifier exists first */
    if (kh->id >= mgr_task_get_num()) {
        pr_err("invalid handle identifier!");
        /* this id is invalid */
        goto err;
    }
    /* execute handle matching on u32 */
    cell_handle = ktaskh_to_taskh(&task_table[kh->id].handle);
    if (unlikely(*cell_handle != h)) {
        /* handle do not match */
        pr_err("handle do not match!");
        goto err;
    }
    tsk = &task_table[kh->id];
err:
    return tsk;
}

kstatus_t mgr_task_get_handle(uint32_t label, taskh_t *handle)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const taskh_t *cell_handle;
    for (uint8_t i = 0; i < mgr_task_get_num(); ++i) {
        task_t *t = &task_table[i];
        uint32_t cell_label = t->metadata->label;
        if (cell_label == label) {
            cell_handle = ktaskh_to_taskh(&t->handle);
            memcpy(handle, cell_handle, sizeof(taskh_t));
            status = K_STATUS_OKAY;
            goto end;
        }
    }
end:
    return status;
}


/**
 * @fn given a task handler, return the corresponding stack frame pointer
 *
 * binary search on task_table
 */
kstatus_t mgr_task_get_sp(taskh_t t, stack_frame_t **sp)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || sp == NULL)) {
        goto end;
    }
    *sp = tsk->sp;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn given a task handler, return the corresponding stack frame pointer
 *
 * binary search on task_table
 */
kstatus_t mgr_task_get_state(taskh_t t, job_state_t *state)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || state == NULL)) {
        goto end;
    }
    /*@ assert \valid(state); */
    *state = tsk->state;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn given a task handler, set the corresponding stack frame pointer
 */
kstatus_t mgr_task_set_sp(taskh_t t, stack_frame_t *newsp)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || newsp == NULL)) {
        goto end;
    }
    /** TODO: adding security sanitation here ? or elsewhere ? */
    tsk->sp = newsp;
    status = K_STATUS_OKAY;
end:
    return status;
}

/*@
    requires job_state_is_valid(state) == \true;
  */
kstatus_t mgr_task_set_state(taskh_t t, job_state_t state)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL)) {
        goto end;
    }
    tsk->state = state;
    status = K_STATUS_OKAY;
end:
    return status;
}

secure_bool_t mgr_task_is_idletask(const taskh_t t)
{
    secure_bool_t res = SECURE_FALSE;
    task_t * tsk = task_get_from_handle(t);

    if (tsk->metadata->label == SCHED_IDLE_TASK_LABEL) {
        res = SECURE_TRUE;
    }
    return res;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
taskh_t mgr_task_get_autotest(void)
{
    /* idle is always the first one */
    ktaskh_t kt = task_table[0].handle;
    const taskh_t *h = ktaskh_to_taskh(&kt);
    /*@ assert \valid(h); */
    return *h;
}
#endif

taskh_t mgr_task_get_idle(void)
{
    /* idle is always the last one */
    ktaskh_t kt = task_table[mgr_task_get_num() - 1].handle;
    const taskh_t *h = ktaskh_to_taskh(&kt);
    /*@ assert \valid(h); */
    return *h;
}

/**
 * @fn return metadata for a given handler (const)
 */
kstatus_t mgr_task_get_metadata(taskh_t t, const task_meta_t **tsk_meta)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || tsk_meta == NULL)) {
        goto end;
    }
    /*@ assert \valid(tsk_meta); */
    *tsk_meta = tsk->metadata;
    status = K_STATUS_OKAY;
end:
    return status;
}

/*
 * Forge a stack context
 */
stack_frame_t *mgr_task_initialize_sp(uint32_t rerun, size_t sp, size_t pc, size_t got)
{
    stack_frame_t *frame = __thread_init_stack_context(rerun, sp, pc, got);
    return frame;
}

/**
 * @brief return the task handler owner of the device handler d
 *
 * @param d: the device handler to search
 * @param t: the task handler reference to update
 *
 * @return:
 *  K_STATUS_OKAY if the device is found in any of the tasks
 *  K_SECURITY_CORRUPTION if task_table is corrupted
 *  K_ERROR_NOENT if devh is not found
 */
kstatus_t mgr_task_get_device_owner(devh_t d, taskh_t *t)
{
    kstatus_t status = K_ERROR_NOENT;
    /* for all tasks... */
    for (uint8_t i = 0; i < mgr_task_get_num(); ++i) {
        if (unlikely(task_table[i].metadata == NULL)) {
            /* should not happen if init done (and thus numtask valid) */
            status = K_SECURITY_CORRUPTION;
            goto end;
        }
        /* for all devices of a task... */
        for (uint8_t dev = 0; dev < task_table[i].metadata->num_devs; ++i) {
            if (task_table[i].metadata->devs[dev] == d) {
                    /* task metadata hold the same dev handle as requested */
                    memcpy(t, &task_table[i].handle, sizeof(taskh_t));
                    status = K_STATUS_OKAY;
                    goto end;
            }
        }
    }
end:
    return status;
}

/**
 * @brief starting userspace tasks
 *
 * Here, we start idle, which is responsible for directly call yield() so that
 * the scheduler will elect() the task to execute.
 *
 * This function switch to userspace and never returns.
 */
void __attribute__((noreturn)) mgr_task_start(void)
{
    stack_frame_t * sp;
    const taskh_t *idleh;
    size_t pc = 0;
    const task_meta_t *idle_meta = task_idle_get_meta();
    idleh = ktaskh_to_taskh(&task_table[mgr_task_get_num() - 1].handle);
    if (unlikely(mgr_task_get_sp(*idleh, &sp) != K_STATUS_OKAY)) {
        pr_err("failed to get idle function handle!");
        goto err;
    };
    pc = (size_t)(idle_meta->s_text + idle_meta->entrypoint_offset);
    /* at startup, sched return idle */
    mgr_mm_map_task(*idleh);
    pr_info("spawning thread, pc=%p, sp=%p", pc, sp);
    mgr_task_set_userspace_spawned();
    /*
     * idle thread is started as privileged thread and drop right to user immediately at entry point
     */
    __platform_spawn_thread(pc, sp, THREAD_MODE_KERNEL);
    __builtin_unreachable();
err:
    panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    __builtin_unreachable();
}

/*
 * TODO: adding requires tsk in [ task_t vector ];
 */
kstatus_t task_set_job_layout(task_t * const tsk)
{
    kstatus_t status;
    /*@ assert \valid_read(tsk); */
    task_meta_t const * meta = tsk->metadata;
     /* mapping task data region first */
    const taskh_t *t = ktaskh_to_taskh(&tsk->handle);
    /*@ assert \valid_read(kt); */
    if (unlikely(mgr_mm_map_task(*t) != K_STATUS_OKAY)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    /* copy got, if non-null */
    if (likely(meta->got_size)) {
        size_t got_source = meta->s_text + \
                             ROUND_UP(meta->text_size, __WORDSIZE);
        size_t got_start  = meta->s_svcexchange + \
                             CONFIG_SVC_EXCHANGE_AREA_LEN;
        pr_debug("[task handle %08x] copy %u bytes of .got from %p to %p", meta->got_size, got_source, got_start);
        memcpy((void*)got_start, (void*)got_source, meta->got_size);
    }
    /* copy data segment if non null */
    if (likely(meta->data_size)) {
        size_t data_source = meta->s_text + \
                             ROUND_UP(meta->text_size, __WORDSIZE) + \
                             ROUND_UP(meta->got_size, __WORDSIZE);
        size_t data_start =  meta->s_svcexchange + \
                             CONFIG_SVC_EXCHANGE_AREA_LEN + \
                             ROUND_UP(meta->got_size, __WORDSIZE);
        pr_debug("[task handle %08x] copy %u bytes of .data from %p to %p", meta->data_size, data_source, data_start);
        memcpy((void*)data_start, (void*)data_source, meta->data_size);
    }
    /* zeroify bss if non-null */
    if (likely(meta->bss_size)) {
        size_t bss_start =  meta->s_svcexchange + \
                            CONFIG_SVC_EXCHANGE_AREA_LEN + \
                            ROUND_UP(meta->got_size, __WORDSIZE) + \
                            ROUND_UP(meta->data_size, __WORDSIZE);
        pr_debug("[task handle %08x] zeroify %u bytes of .bss at addr %p", meta->bss_size, bss_start);
        memset((void*)bss_start, 0x0, meta->bss_size);
    }
    /* zeroify SVC Exchange */
    memset((void*)meta->s_svcexchange, 0x0, CONFIG_SVC_EXCHANGE_AREA_LEN);
    status = K_STATUS_OKAY;
err:
    return status;
}


/**
 * About events manipulation in tasks
 */
kstatus_t mgr_task_push_int_event(uint32_t IRQn, taskh_t dest)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const ktaskh_t *kt = taskh_to_ktaskh(&dest);
    /*@ assert \valid_read(kt); */
    task_t * tsk = task_get_from_handle(dest);
    job_state_t state;
    if (unlikely(tsk->num_ints == TASK_EVENT_QUEUE_DEPTH)) {
        status = K_ERROR_BUSY;
        goto err;
    }
    tsk->ints[tsk->num_ints] = IRQn;
    tsk->num_ints++;

    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_load_int_event(taskh_t context)
{
    kstatus_t status = K_ERROR_NOENT;
    return status;
}


kstatus_t mgr_task_push_ipc_event(uint32_t len, taskh_t source, taskh_t dest)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(dest);
    job_state_t state;

    if (unlikely(tsk == NULL)) {
        goto err;
    }
    const ktaskh_t *ksrc = taskh_to_ktaskh(&source);
    tsk->ipcs[ksrc->id] = len;
    status = K_STATUS_OKAY;
err:
    return status;
}

#if CONFIG_BUILD_TARGET_AUTOTEST
static uint8_t autotest_exchangebuf[CONFIG_SVC_EXCHANGE_AREA_LEN];
#endif

kstatus_t mgr_task_load_ipc_event(taskh_t context)
{
    kstatus_t status = K_ERROR_NOENT;
    task_t * current = task_get_from_handle(context);

    if (unlikely(current == NULL)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }

    for (uint8_t idx = 0; idx < mgr_task_get_num(); ++idx) {
        uint8_t len = current->ipcs[idx];
        if (len > 0) {
            task_t *source = &task_table[idx];
            const taskh_t *source_handle = ktaskh_to_taskh(&source->handle);
            /* get source and dest exchange area address (metadata) */
            uint8_t *source_svcexch = (uint8_t*)source->metadata->s_svcexchange;
            exchange_event_t *dest_svcexch = (exchange_event_t *)current->metadata->s_svcexchange;

#if CONFIG_BUILD_TARGET_AUTOTEST
            /* in the very specific case of autotest, when sending to ourself
             * we can't execute a single-copy between the very same buffer
             * No need to map here as source & dest are equal and dest svc_exhange
             * is already mapped.
             * Note: In armv8m, double map would even lead to HardFault
             */
            memcpy(&autotest_exchangebuf[0], source_svcexch, CONFIG_SVC_EXCHANGE_AREA_LEN);
            source_svcexch = autotest_exchangebuf;
#else
            /* mapping source svc exhvange area */
            if (unlikely((status = mgr_mm_map_svcexchange(*source_handle)) != K_STATUS_OKAY)) {
                goto end;
            }
#endif
            /* set T,L values from TLV */
            dest_svcexch->type = EVENT_TYPE_IPC;
            dest_svcexch->length = len + sizeof(taskh_t);
            dest_svcexch->magic = 0x4242; /** FIXME: define a magic shared with uapi */
            memcpy(dest_svcexch->data, source_handle, sizeof(taskh_t));
            memcpy(&dest_svcexch->data[4], source_svcexch, len);
            /* handle scheduling, awake source */
#ifndef CONFIG_BUILD_TARGET_AUTOTEST
            /* in autotest, no need to schedule again ourself, as already ready */
            mgr_task_set_sysreturn(*source_handle, STATUS_OK);
            mgr_task_set_state(*source_handle, JOB_STATE_READY);
            sched_schedule(*source_handle);
#endif
            /* clear local cache */
            current->ipcs[idx] = 0;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
end:
    return status;
}

kstatus_t mgr_task_push_sig_event(uint32_t signal, taskh_t source, taskh_t dest)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(dest);
    job_state_t state;

    if (unlikely(tsk == NULL)) {
        goto err;
    }
    /* now we are sure that dest exists and is valid */
    const ktaskh_t *kdesth = taskh_to_ktaskh(&dest);
    if (tsk->sigs[kdesth->id] != 0) {
        /* a previous signal already exist */
        status = K_ERROR_BUSY;
        goto err;
    }
    tsk->sigs[kdesth->id] = signal;
    if (likely(mgr_task_get_state(dest, &state) != K_STATUS_OKAY)) {
        goto err;
    }
    if (likely(state == JOB_STATE_WAITFOREVENT)) {
        mgr_task_set_state(dest, JOB_STATE_READY);
        sched_schedule(dest);
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_load_sig_event(taskh_t context)
{
    kstatus_t status = K_ERROR_NOENT;
    task_t * current = task_get_from_handle(context);

    if (unlikely(current == NULL)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }

    for (uint8_t idx = 0; idx < mgr_task_get_num(); ++idx) {
        uint8_t signal = current->sigs[idx];
        if (signal > 0) {
            task_t *source = &task_table[idx];
            job_state_t state;
            const taskh_t *source_handle = ktaskh_to_taskh(&source->handle);
            /* get source and dest exchange area address (metadata) */
            exchange_event_t *dest_svcexch = (exchange_event_t *)current->metadata->s_svcexchange;
            /* set T,L values from TLV */
            dest_svcexch->type = EVENT_TYPE_SIGNAL;
            dest_svcexch->length = 2*(sizeof(uint32_t));
            dest_svcexch->magic = 0x4242; /** FIXME: define a magic shared with uapi */
            uint32_t *sigdata = (uint32_t*)&dest_svcexch->data;
            sigdata[0] = *source_handle;
            sigdata[1] = signal;
            /* clear local cache */
            current->sigs[idx] = 0;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
end:
    return status;
}

kstatus_t mgr_task_add_resource(taskh_t t, uint8_t resource_id, layout_resource_t resource)
{
    kstatus_t status;
    task_t *cell;

    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    if (unlikely(resource_id >= TASK_MAX_RESSOURCES_NUM)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    memcpy(&cell->layout[resource_id], &resource, sizeof(layout_resource_t));
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief removing a resource from task context, based on its identifier
 * @warning this is the layout id, not the region id !
 */
kstatus_t mgr_task_remove_resource(taskh_t t, uint8_t resource_id)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    mpu_forge_unmapped_ressource(resource_id, &cell->layout[resource_id]);
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_get_layout_from_handle(taskh_t t,
                                          const layout_resource_t **layout)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely(layout == NULL)) {
        goto err;
    }
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    *layout = &cell->layout[0];
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_set_jobreturn(taskh_t t, uint32_t returncode)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    cell->returncode = returncode;
    status = K_STATUS_OKAY;
err:
    return status;
}

/** TODO: fix handle management before coding framac_get_handle() */
/*@
    behavior badsysret:
        assumes !\valid(sysret);
        assigns \nothing;
        ensures \result == K_ERROR_INVPARAM;
    behavior badhandle:
        assumes \valid(sysret);
        assumes !\valid(framac_get_handle(t));
        assigns \nothing;
        ensures \result == K_ERROR_INVPARAM;
    behavior unvstate:
        assumes \valid(sysret);
        assumes \valid(framac_get_handle(t));
        assumes !framac_sysret_is_set(framac_get_handle(t));
        assigns \nothing;
        ensures \result == K_ERROR_INVSTATE;
    behavior get:
        assumes \valid(sysret);
        assumes \valid(framac_get_handle(t));
        assumes framac_sysret_is_set(framac_get_handle(t));
        assigns sysret;
        ensures \result = framac_get_handle(t)->sysreturn;

    complete behaviors;
    disjoint behaviors;
*/
kstatus_t mgr_task_get_sysreturn(taskh_t t, Status *sysret)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely(sysret == NULL)) {
        goto err;
    }
    /*@ assert \valid(status); */
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    if (unlikely(cell->sysretassigned == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto err;
    }
    *sysret = cell->sysreturn;
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_clear_sysreturn(taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    if (unlikely(cell->sysretassigned == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto err;
    }
    cell->sysretassigned = SECURE_FALSE;
err:
    return status;
}

kstatus_t mgr_task_set_sysreturn(taskh_t t, Status sysret)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    cell->sysreturn = sysret;
    cell->sysretassigned = SECURE_TRUE;
err:
    return status;
}
