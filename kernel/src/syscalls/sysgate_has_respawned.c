// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>
#include <uapi/types.h>

/**
 * @brief syscall gate handling for task respawned check.
 *
 * This syscall is used by userspace to check if the current task has been respawned or not.
 * This is a simple syscall, that do not require any parameter, and return STATUS_OK if
 * the task has been respawned, or STATUS_AGAIN if the task has not been respawned.
 *
 * There is no requirement for userspace tasks to call this syscall, but it can be useful
 * if the userspace task aim to react to potential respawn.
 * For e.g. this syscall is used in autotest mode to check the effectiveness of the
 * respawn mechanism, by checking that the task has been respawned after a voluntary exit.
 */
stack_frame_t *gate_has_respawned(stack_frame_t *frame)
{
    taskh_t current = sched_get_current();
    if (mgr_task_has_respawned(current) == SECURE_TRUE) {
        /* if the task has been respawned, return OK */
        mgr_task_set_sysreturn(current, STATUS_OK);
    } else {
        /* if the task has not been respawned, return AGAIN, has by now, this is not the case */
        mgr_task_set_sysreturn(current, STATUS_AGAIN);
    }
    return frame;
}
