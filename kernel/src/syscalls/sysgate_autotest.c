// SPDX-FileCopyrightText: 2025 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/thread.h>
#include <sentry/ktypes.h>
#include <sentry/managers/task.h>
#include <sentry/managers/security.h>
#include <sentry/sched.h>
#include <sentry/zlib/math.h>


stack_frame_t *gate_autotest_set_self_capa(stack_frame_t *frame, uint32_t capa)
{
    taskh_t current = sched_get_current();
    if (!IS_POW2(capa)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    mgr_security_set_capa(capa);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}

stack_frame_t *gate_autotest_clear_self_capa(stack_frame_t *frame, uint32_t capa)
{
    taskh_t current = sched_get_current();
    if (!IS_POW2(capa)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    mgr_security_clear_capa(capa);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
