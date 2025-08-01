// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <uapi/types.h>
#include <uapi/dma.h>
#include <uapi/platform.h>
#include <sentry/managers/dma.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>
#include <string.h>

#ifdef CONFIG_HAS_GPDMA
/* compile time check for SVC exchange size constraint */
static_assert(SENTRY_SVCEXCHANGE_LEN >= sizeof(gpdma_stream_cfg_t));
#endif

stack_frame_t *gate_dma_getinfo(stack_frame_t *frame, dmah_t dmah)
{
    taskh_t current = sched_get_current();
    Status sysret = STATUS_NO_ENTITY;
#ifdef CONFIG_HAS_GPDMA
    const task_meta_t * meta;
    taskh_t owner;
    size_t svcexch;
    gpdma_stream_cfg_t const * kinfo = NULL;

    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_dma_get_owner(dmah, &owner) != K_STATUS_OKAY)) {
        sysret = STATUS_INVALID;
        goto end;
    }
    if (unlikely(owner != current)) {
        sysret = STATUS_DENIED;
        goto end;
    }
    if (unlikely(mgr_security_has_capa(current, CAP_DEV_DMA) != SECURE_TRUE)) {
        sysret = STATUS_DENIED;
        goto end;
    }
    if (unlikely(mgr_dma_get_info(dmah, &kinfo) != K_STATUS_OKAY)) {
        sysret = STATUS_INVALID;
        goto end;
    }
    svcexch = meta->s_svcexchange;
    memcpy((void *)svcexch, kinfo, sizeof(gpdma_stream_cfg_t));
    sysret = STATUS_OK;
end:
#endif
    mgr_task_set_sysreturn(current, sysret);
    return frame;
}
