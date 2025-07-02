// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <uapi/uapi.h>
#include <test_cycles.h>
#include <test_sleep.h>
#include <test_yield.h>
#include <test_random.h>
#include <test_ipc.h>
#include <test_handle.h>
#include <test_signal.h>
#include <test_gpio.h>
#include <test_map.h>
#include <test_shm.h>
#include <test_dma.h>
#include <test_irq.h>

uint32_t __stack_chk_guard = 0;

/**
 * NOTE: autotest task is a 'bare' Sentry kernel task, meaning that there is
 * no build system calculating each section and mapping the task on the target.
 *
 * As a consequence, the kernel is not able to determine the size of the .data
 * and .bss sections, and these two values are hardcoded (data and bss set to 0)
 * This means that autotest task MUST NOT use any globals.
 *
 * Of course, this restriction do not impact standard userspace apps :-)
 */

void __attribute__((no_stack_protector, used, noreturn)) autotest(uint32_t label, uint32_t seed)
{
    bool test_finished = false;
    /* update SSP value with given seed */
    __stack_chk_guard = seed;
    const char *welcommsg="hello this is autotest!\n";
    const char *testmsg="starting test suite...\n";

    printf(welcommsg);
    printf(testmsg);
    printf("AUTOTEST START");
#ifdef CONFIG_TEST_YIELD
    test_yield();
#endif
#ifdef CONFIG_TEST_HANDLES
    test_handle();
#endif
#ifdef CONFIG_TEST_SIGNALS
    test_signal();
#endif
#ifdef CONFIG_TEST_IPC
    test_ipc();
#endif
#ifdef CONFIG_TEST_RANDOM
    test_random();
#endif
#ifdef CONFIG_TEST_CYCLES
    test_cycles();
#endif
#ifdef CONFIG_TEST_SLEEP
    test_sleep();
#endif
#ifdef CONFIG_TEST_GPIO
    test_gpio();
#endif
#ifdef CONFIG_TEST_DEVICES
    test_map();
#endif
#ifdef CONFIG_TEST_SHM
    test_shm();
#endif
#ifdef CONFIG_TEST_DMA
    test_dma();
#endif
#ifdef CONFIG_TEST_IRQ
    test_irq();
#endif
    printf("AUTOTEST END");


    /* all tests finished, leaving */
    __sys_exit(0);
    __builtin_unreachable();
}
