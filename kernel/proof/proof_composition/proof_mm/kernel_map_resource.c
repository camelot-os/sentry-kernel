// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>

#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/panic.h>

int prepare_startup(void)
{
    int res = 1;
    /* early init phase */
    mgr_interrupt_early_init();
    /* platform init phase */
    mgr_clock_init(); /* init bus clocking, needed for debug */
    mgr_io_init();  /* I/O probing and init, needed for debug */
    #ifndef CONFIG_BUILD_TARGET_RELEASE
    mgr_debug_init();
    #endif
        /* initialize security manager */
    if (unlikely(mgr_security_init() != K_STATUS_OKAY)) {
        goto end;
    }
    /* initialize memory manager */
    if (unlikely(mgr_mm_init() != K_STATUS_OKAY)) {
        goto end;
    };
    /* user interrupts manager init */
    if (unlikely(mgr_interrupt_init() != K_STATUS_OKAY)) {
        goto end;
    }
    /* delays and scheduler init */
    if (unlikely(mgr_time_init() != K_STATUS_OKAY)) {
        goto end;
    }
    /* tasks initialization (probing) */
    if (unlikely(mgr_task_init() != K_STATUS_OKAY)) {
        goto end;
    }
    res = 0;
end:
    return res;
}

int map_resource(void)
{
    /*
     * here we define unpredicable resource ID and layout,
     * to cover any possible resource structure input values, so
     * that we can demonstrate that only valid (aligned, non-overlapping)
     * resources are mapped.
     * NOTE: this do not check the resource ownership, as this is done by
     * the task manager itself.
     */
    volatile uint8_t resource_id = 0;
    volatile layout_resource_t resource;
    if (prepare_startup() != 0) {
        return -1;
    }
    /* as we do not check ownership but only mapping, we use idle task as vehicle */
    mgr_task_add_resource(mgr_task_get_idle(), resource_id, resource);
    return 0;
}
