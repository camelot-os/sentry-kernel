// SPDX-FileCopyrightText: 2025 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/thread.h>
#include <sentry/ktypes.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>


stack_frame_t *gate_autotest_set_self_capa(stack_frame_t *frame, uint32_t capa)
{
    taskh_t current = sched_get_current();
    mgr_task_set_sysreturn(current, STATUS_OK);
    return frame;
}

stack_frame_t *gate_autotest_clear_self_capa(stack_frame_t *frame, uint32_t capa)
{
    taskh_t current = sched_get_current();
    mgr_task_set_sysreturn(current, STATUS_OK);
    return frame;
}
