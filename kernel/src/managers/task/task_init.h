// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_INIT_H
#define TASK_INIT_H

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include "task_core.h"

/*@
  @ assigns \nothing;
  */
uint32_t mgr_task_get_num(void);

void mgr_task_set_userspace_spawned(void);

/*
 * The following functions are exported locally to the task manager module, in order
 * to share the task initialization logic between the boot time initialization FSM and
 * the task respawn handling, as both of them require to forge the task local info and
 * to map the task memory layout.
 * These function do not handle the FSM-related state check, leaving this responsibility
 * to each FSM logic.
 */

kstatus_t task_do_initiate_localinfo(task_meta_t const * const meta, task_t *tsk);

kstatus_t task_do_map(task_t * tsk);

#endif/*!TASK_INIT_H*/
