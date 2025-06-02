// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <uapi/uapi.h>

#include "arch/control.h"

/**
 * This is the lonely .data variable of idle, used for SSP
 */
uint32_t __stack_chk_guard = 0;

void idle_task(unsigned int label, unsigned int seed)
{
    const char *welcommsg="hello this is idle!\n";
    const char *yieldmsg="yielding for scheduler...\n";

    /* update SSP value with given seed */
    __stack_chk_guard = seed;

    copy_to_kernel(welcommsg, 20);
    __sys_log(20);

    copy_to_kernel(yieldmsg, 26);
    __sys_log(26);
    /* TODO: yield() first, to force task scheduling */
    __sys_sched_yield();

    do {
        /* entering LP mode */
        //sys_manage_cpu_sleep(CPU_SLEEP_WAIT_FOR_INTERRUPT);
        /* rise from LP, force task election */
        __sys_sched_yield();
    } while (1);
}

/**
 * NOTE: idle task is a 'bare' Sentry kernel task, meaning that there is
 * no build system calculating each section and mapping the task on the target.
 *
 * As a consequence, the kernel is not able to determine the size of the .data
 * and .bss sections, and these two values are hardcoded (data and bss set to 0)
 * This means that idle task MUST NOT use any globals.
 *
 * Of course, this restriction do not impact standard userspace apps :-)
 */

void __attribute__((no_stack_protector, used, noreturn)) idle(uint32_t label, uint32_t seed)
{
    __switch_to_userspace(idle_task, label, seed);
}
