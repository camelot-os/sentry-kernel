// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>
/**
 * Note: the selected scheduler depends on the Kconfig level configuration
 * This means that in order to cover all scheduler, this file needs to be compiled (and frama-C run)
 * for each scheduler configuration.
 * Default config is the Round-Robin Multi-Queue (RRMQ) scheduler.
 */
#include <inttypes.h>
#include <uapi/types.h>
#include <sentry/ktypes.h>
#include <sentry/managers/task_metadata.h>
#include <sentry/job.h>
#include <sentry/sched.h>


/**
 * Here we stub the mgr_task_get_metadata function in order to allow the scheduler to be tested
 * independently of the task manager. The goal is to delivers unpredictable metadata content,
 * that permit to thoroughly test the scheduler's behavior under various metadata scenarios.
 *
 */

volatile task_meta_t metadata;
volatile stack_frame_t frame;

/* make the metadata content unknown but assigned to Frama-C */


/*@
  assigns \nothing;
 */
kstatus_t mgr_task_get_metadata(taskh_t taskh, const task_meta_t **metadata)
{
    *metadata = Frama_C_make_unknown((void*)&metadata, sizeof(task_meta_t));
    return K_STATUS_OKAY;
}

/*@ assigns \nothing; */
void kernel_sched(void)
{
    taskh_t taskh;

    Frama_C_make_unknown(&taskh, sizeof(taskh));
    Frama_C_make_unknown(&frame, sizeof(stack_frame_t));

    /* Initialize the scheduler and perform scheduling operations, no external lib required */
    sched_init();
    /* external symbol limited to mgr_task_get_metadata() stubbed above */
    sched_schedule(taskh);
    sched_elect();
    sched_get_current();
    sched_refresh(&frame);
    sched_get_current();
}
