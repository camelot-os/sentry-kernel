// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include <sentry/arch/asm-generic/thread.h>

#include <sentry/arch/asm-generic/handler-svc-lut.h>

//TODO: Fix uapi type include
#define STATUS_NO_ENTITY 3

static stack_frame_t *lut_unsuported(stack_frame_t *frame) {
    mgr_task_set_sysreturn(sched_get_current(), STATUS_NO_ENTITY);
    return frame;
}

static const lut_svc_handler svc_lut[] = {
    lut_unsuported,
};


#define SYSCALL_NUM ARRAY_SIZE(svc_lut)

lut_svc_handler const *svc_lut_get(void) {
    return &svc_lut[0];
}
size_t svc_lut_size(void) {
    return SYSCALL_NUM;
}