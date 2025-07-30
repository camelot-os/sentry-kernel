// SPDX-FileCopyrightText: 2025 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/managers/security.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/arch/asm-generic/platform.h>
#include "entropy.h"

#if CONFIG_BUILD_TARGET_AUTOTEST
/**
 * @brief autotest-specific dynamic capability set
 *
 * In non-autotest mode, all tasks have their capablity set added through the
 * corresponding rodata field that hold overall build-time informations, in the task
 * metadata area, kept in NVM.
 * In autotest mode, this field is used in order to hold the autotest-exclusive
 * overload of the capability set. This is made in the security manager instead of the
 * task manager (that hold all task-related informations and accessors) in order to
 * reduce as much as possible the capability checking mode footprint in the
 * kernel sources.
 * This field is set at boot time with the build-time configured capability set in the
 * autotest metadata-field (see task manager about this) and can be overloaded using this
 * field.
 * autotest being single threaded and accedded only during initialization and through autotest
 * syscall, no race condition on this field is possible, even in SMP mode.
 * XXX: this could be verified using Frama-C thread analysis model or using tool such as CodeSonar
 * to demonstrate this.
 */
static uint32_t autotest_cap_set;
#endif

kstatus_t mgr_security_init(void)
{
    kstatus_t status;
    pr_info("initialize security manager...");
    status = mgr_security_entropy_init();
#ifndef CONFIG_BUILD_TARGET_DEBUG
    pr_info("Forbid unaligned access");
    __platform_enforce_alignment();
#endif
#if CONFIG_BUILD_TARGET_AUTOTEST
    /* set bootup capas for autotest here */
    autotest_cap_set = 0;
#ifdef CONFIG_TEST_DEVICES
    autotest_cap_set |= CAP_DEV_BUSES;
#endif
#ifdef CONFIG_TEST_GPIO
    autotest_cap_set |= CAP_DEV_IO;
#endif
#ifdef CONFIG_TEST_RANDOM
    autotest_cap_set |= CAP_CRY_KRNG;
#endif
#ifdef CONFIG_TEST_SHM
    autotest_cap_set |= CAP_MEM_SHM_OWN;
    autotest_cap_set |= CAP_MEM_SHM_USE;
    autotest_cap_set |= CAP_MEM_SHM_TRANSFER;
#endif
#ifdef CONFIG_TEST_DMA
    /** note: DMA M2M transfers are made between SHMs, requiring SHM perms */
    autotest_cap_set |= CAP_DEV_DMA;
    autotest_cap_set |= CAP_MEM_SHM_OWN;
    autotest_cap_set |= CAP_MEM_SHM_USE;
#endif
#ifdef CONFIG_TEST_IRQ
    autotest_cap_set |= CAP_DEV_TIMER;
#endif
#endif /*CONFIG_BUILD_TARGET_AUTOTEST*/
    return status;
}

kstatus_t mgr_security_get_capa(taskh_t tsk, uint32_t *capas)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const task_meta_t *meta;

    if (unlikely(capas == NULL)) {
        goto end;
    }
#if CONFIG_BUILD_TARGET_AUTOTEST
    *capas = autotest_cap_set;
#else
    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    *capas = meta->capabilities;
#endif
end:
    return status;
}

secure_bool_t mgr_security_has_dev_capa(taskh_t tsk)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

#if CONFIG_BUILD_TARGET_AUTOTEST
    if (CAP_DEV_MASK & autotest_cap_set) {
        res = SECURE_TRUE;
        goto end;
    }
#endif
    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if ((meta->capabilities & CAP_DEV_MASK) != 0) {
        res = SECURE_TRUE;
    }
end:
    return res;
}

secure_bool_t mgr_security_has_sys_capa(taskh_t tsk)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

#if CONFIG_BUILD_TARGET_AUTOTEST
    if (CAP_SYS_MASK & autotest_cap_set) {
        res = SECURE_TRUE;
        goto end;
    }
#endif
    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if ((meta->capabilities & CAP_SYS_MASK) != 0) {
        res = SECURE_TRUE;
    }
end:
    return res;
}


secure_bool_t mgr_security_has_capa(taskh_t tsk, capability_t  capa)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

#if CONFIG_BUILD_TARGET_AUTOTEST
    if (capa & autotest_cap_set) {
        res = SECURE_TRUE;
        goto end;
    }
#endif
    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if (meta->capabilities & capa) {
        res = SECURE_TRUE;
    }
end:
    return res;
}

secure_bool_t mgr_security_has_oneof_capas(taskh_t tsk, uint32_t capas)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

#if CONFIG_BUILD_TARGET_AUTOTEST
    if (capas & autotest_cap_set) {
        res = SECURE_TRUE;
        goto end;
    }
#endif
    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if (meta->capabilities & capas) {
        res = SECURE_TRUE;
    }
end:
    return res;
}



#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_security_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    uint32_t seed;
    uint64_t start;
    uint64_t stop;
    uint64_t min = 0;
    uint64_t max = 0;
    uint64_t average = 0;
    uint32_t failures = 0;
    pr_autotest("START execute 256 entropy generation from entropy source");
    /* executing 256 random seed requests */
    for (uint32_t i=0; i < 256; ++i) {
        start = systime_get_cycle();
        if (unlikely(mgr_security_entropy_generate(&seed) != K_STATUS_OKAY)) {
            failures++;
        }
        stop = systime_get_cycle();
        uint64_t duration = stop - start;
        if (duration > max) {
            max = duration;
        }
        if ((min == 0) || (duration < min)) {
            min = duration;
        }
        average += duration;
    }
    /* average div 256 */
    average >>= 8;
    pr_autotest("entropy_generate min time: %llu", min);
    pr_autotest("entropy_generate max time: %llu", max);
    pr_autotest("entropy_generate average time: %llu", average);
    pr_autotest("entropy_generate failures: %llu", failures);
    pr_autotest("END");

    return status;
}

/**
 * @brief add a capability to the autotest capability set
 */
kstatus_t mgr_security_set_capa(capability_t cap)
{
    autotest_cap_set |= cap;
    return K_STATUS_OKAY;
}

/**
 * @brief remove a capability from the autotest capability set
 */
kstatus_t mgr_security_clear_capa(capability_t cap)
{
    autotest_cap_set &= ~cap;
    return K_STATUS_OKAY;
}
#endif
