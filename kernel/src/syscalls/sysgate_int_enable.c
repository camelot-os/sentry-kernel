// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi/uapi.h>
#include <sentry/syscalls.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

/**
 * @fn gate_int_enable - enable at NVIC level given IRQ (IT controller unmask)
 *
 * @param[in] frame current job's frame. Not updated here
 * @param[in] IRQn IRQ number to acknowledge
 *
 * @return current job frame (no modification)
 */
stack_frame_t *gate_int_enable(stack_frame_t *frame, uint16_t IRQn)
{
    taskh_t current = sched_get_current();
    taskh_t owner;
    devh_t  dev;
    task_meta_t meta;

    if (unlikely(mgr_security_has_dev_capa(current) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    /* get the device owning the interrupt */
    if (unlikely(mgr_device_get_devh_from_interrupt(IRQn, &dev) != K_STATUS_OKAY)) {
        /* interrupt with no known device ???? */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* when reach this point, the IRQn is valid, as it exists at kernel level */
    /*@ assert IRQn < __NVIC_VECTOR_LEN; */
    /* get the task owning the device */
    if (unlikely(mgr_device_get_owner(dev, &owner) != K_STATUS_OKAY)) {
        /* user interrupt with no owning task. Should not happen as the kernel do not hold any IRQ */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* push the inth event into the task input events queue */
    if (unlikely(mgr_interrupt_enable_irq(IRQn) != K_STATUS_OKAY)) {
        /* should not rise while IRQ ownership has been checked! see dts file */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
