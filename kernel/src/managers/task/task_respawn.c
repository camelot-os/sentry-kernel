// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>
#include "task_core.h"
#include "task_init.h"

/**
 * @file Sentry task manager respawn handling.
 *
 * This function is not FSM-based because the respawning mechanism is simple enough.
 */


kstatus_t task_respawn_job(taskh_t task_handle)
{
    kstatus_t status = K_ERROR_UNKNOWN;
    task_t *task_ctx = task_get_from_handle(task_handle);
    if (unlikely(task_ctx == NULL)) {
        /* should never happen*/
        pr_err("invalid task context");
        status = K_ERROR_NOENT;
        goto end;
    }
    if (task_ctx->state != JOB_STATE_FINISHED) {
        /*
         * scheduling policy on respawn to be defined in a Kconfig model way. By now, we
         * do not allow faulting jobs to be rescheduled. As this is a normal behavior,
         * we yet return STATUS_OK to caller
         * Note that in that case, as the job is not rescheduled, the state is set to NON_SENSE,
         * so that if the job is elected again, it will generate a voluntary panic() due to invalid state.
         */
        task_ctx->sysreturn = STATUS_NON_SENSE;
        status = K_STATUS_OKAY;
        goto end;
    }
    /*
     * it is considered, at respawn time, that boot time integrity checks of task metadata
     * have already been performed.
     * We reuse the already populated cell from the task table, as the task is already considered as started,
     * and thus has already a cell reserved in the task table.
     */
    status = task_do_initiate_localinfo(task_ctx->metadata, task_ctx);
    if (unlikely(status != K_STATUS_OKAY)) {
        /*
         * a failure at this step means that the security manager entropy generation failed.
         * This is a critical failure, and is handled by a panic() at upper layer.
         * Such a behavior is not applicative level triggable, meaning that this should not
         * be possible to trigger this failure through a normal userspace behavior, and thus is not
         * considered as a normal behavior, but rather as a critical failure.
         */
        goto end;
    }
    /* from now on, the task has a new handle associated to the newly created job */
    status = task_do_map(task_ctx);
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    /* at respawn time, the task is considered as previously started. The task is then automatically rescheduled */
    status = sched_schedule(*ktaskh_to_taskh(&task_ctx->handle));
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}
