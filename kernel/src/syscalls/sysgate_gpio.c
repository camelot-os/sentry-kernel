// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi/device.h>
#include <uapi/uapi.h>
#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/device.h>
#include <sentry/managers/io.h>
#include <sentry/managers/security.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

/** XXX: using io manager API instead */
#include <bsp/drivers/gpio/pinctrl.h>

static inline secure_bool_t do_own_dev(taskh_t owner, devh_t dev) {
    secure_bool_t res = SECURE_FALSE;
    taskh_t devowner;
    if (unlikely(mgr_device_get_owner(dev, &devowner) != K_STATUS_OKAY)) {
        /* considering previous check, must not fail */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (likely(devowner == owner)) {
        res = SECURE_TRUE;
    } else {
        pr_err("GPIO device not owned");
    }
    return res;
}


stack_frame_t *gate_gpio_set(stack_frame_t *frame, devh_t devhandle, uint8_t io, bool val)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    const devinfo_t *devinfo = NULL;

    if (unlikely(mgr_device_get_info(devhandle, &devinfo) != K_STATUS_OKAY)) {
        pr_err("invalid device");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* disable ownership test in autotest only */
    if (unlikely(do_own_dev(current, devhandle) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_security_has_oneof_capas(current, CAP_DEV_IO | CAP_DEV_BUSES) != SECURE_TRUE)) {
        pr_err("needs IO or BUSES capa");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(io >= devinfo->num_ios)) {
        pr_err("invalid dev IO number");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* TODO: disallow setting GPIO not set in OUTPUT MODE */
    /* XXX: the dt header should abstract the stm32 prefix */
    if (val) {
        if (unlikely(mgr_io_set(devinfo->ios[io].port, devinfo->ios[io].pin) != K_STATUS_OKAY)) {
            pr_err("IO set failed!");
            mgr_task_set_sysreturn(current, STATUS_INVALID);
            goto end;
        }
    } else {
        if (unlikely(mgr_io_reset(devinfo->ios[io].port, devinfo->ios[io].pin) != K_STATUS_OKAY)) {
            pr_err("IO reset failed!");
            mgr_task_set_sysreturn(current, STATUS_INVALID);
            goto end;
        }
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}

stack_frame_t *gate_gpio_get(stack_frame_t *frame, devh_t devhandle, uint8_t io)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    const devinfo_t *devinfo = NULL;
    bool val;
    const task_meta_t *meta;
    uint8_t *svcexch = NULL;


    if (unlikely(mgr_device_get_info(devhandle, &devinfo) != K_STATUS_OKAY)) {
        pr_err("invalid device handle");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(do_own_dev(current, devhandle) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_security_has_oneof_capas(current, CAP_DEV_IO | CAP_DEV_BUSES) != SECURE_TRUE)) {
        pr_err("capa IO or BUSES required");
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(io >= devinfo->num_ios)) {
        pr_err("invalid dev IO number");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* TODO: disallow getting GPIO not set in INPUT MODE
     * TODO: we should allow access for AF cases though
     */
    if (unlikely(mgr_io_read(devinfo->ios[io].port, devinfo->ios[io].pin, &val) != K_STATUS_OKAY)) {
        pr_err("IO read failed");
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* set value into svcexchange */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint8_t*)meta->s_svcexchange;
    svcexch[0] = val;
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}

stack_frame_t *gate_gpio_reset(stack_frame_t *frame, devh_t devhandle, uint8_t io)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    const devinfo_t *devinfo = NULL;

    if (unlikely(mgr_device_get_info(devhandle, &devinfo) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(do_own_dev(current, devhandle) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_security_has_oneof_capas(current, CAP_DEV_IO | CAP_DEV_BUSES) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(io >= devinfo->num_ios)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* TODO: by now disallow setting GPIO not set in OUTPUT MODE */
    if (unlikely(mgr_io_reset(devinfo->ios[io].port, devinfo->ios[io].pin) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}

stack_frame_t *gate_gpio_toggle(stack_frame_t *frame, devh_t devhandle, uint8_t io)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    const devinfo_t *devinfo = NULL;
    bool val;

    if (unlikely(mgr_device_get_info(devhandle, &devinfo) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(do_own_dev(current, devhandle) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_security_has_oneof_capas(current, CAP_DEV_IO | CAP_DEV_BUSES) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(io >= devinfo->num_ios)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_io_read(devinfo->ios[io].port, devinfo->ios[io].pin, &val) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (val == false) {
        /* TODO: by now disallow setting GPIO not set in OUTPUT MODE */
        if (unlikely(mgr_io_set(devinfo->ios[io].port, devinfo->ios[io].pin) != K_STATUS_OKAY)) {
            mgr_task_set_sysreturn(current, STATUS_INVALID);
            goto end;
        }
    } else {
        if (unlikely(mgr_io_reset(devinfo->ios[io].port, devinfo->ios[io].pin) != K_STATUS_OKAY)) {
            mgr_task_set_sysreturn(current, STATUS_INVALID);
            goto end;
        }
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}

stack_frame_t *gate_gpio_configure(stack_frame_t *frame, devh_t devhandle, uint8_t io)
{
     stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    const devinfo_t *devinfo = NULL;
    bool val;

    if (unlikely(mgr_device_get_info(devhandle, &devinfo) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(do_own_dev(current, devhandle) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_security_has_oneof_capas(current, CAP_DEV_IO | CAP_DEV_BUSES) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(io >= devinfo->num_ios)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    gpio_pinctrl_desc_t desc = {
        .mode = devinfo->ios[io].mode,
        .altfunc = devinfo->ios[io].af,
        .type = devinfo->ios[io].pupdr,
        .speed = devinfo->ios[io].speed,
        .pull_mode = devinfo->ios[io].ppull,
        .port_id = devinfo->ios[io].port,
        .pin = devinfo->ios[io].pin,
    };
    if (unlikely(gpio_pinctrl_configure(desc) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
