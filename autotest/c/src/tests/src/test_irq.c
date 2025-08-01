// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <string.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include <uapi/dma.h>
#include <shms-dt.h>
#include "test_dma.h"
#include <drivers/timer.h>

static devh_t handle;

static void test_irq_spawn_two_it(void)
{
    Status res;
    uint8_t tab[128];
    uint32_t *IRQn;
    uint32_t irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_enable();
    /* waiting 1200ms */
    res = __sys_wait_for_event(EVENT_TYPE_IRQ, 0);
    copy_from_kernel(&tab[0], sizeof(exchange_event_t) + 4);
    ASSERT_EQ(res, STATUS_OK);
    IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
    ASSERT_EQ(*IRQn, irq);
    timer_enable_interrupt();
    timer_enable();
    /* waiting 1200ms */
    res = __sys_wait_for_event(EVENT_TYPE_IRQ, 0);
    copy_from_kernel(&tab[0], sizeof(exchange_event_t) + 4);
    ASSERT_EQ(res, STATUS_OK);
    IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
    ASSERT_EQ(*IRQn, irq);
    return;
}

static void test_irq_spawn_one_it(void)
{
    Status res;
    uint8_t tab[128];
    uint32_t irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_enable();
    /* waiting 1200ms */
    res = __sys_wait_for_event(EVENT_TYPE_IRQ, 0);
    copy_from_kernel(&tab[0], sizeof(exchange_event_t) + 4);
    ASSERT_EQ(res, STATUS_OK);
    uint32_t *IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
    ASSERT_EQ(*IRQn, irq);
    ASSERT_EQ(((exchange_event_t*)tab)->source, handle);
    return;
}


static void test_irq_spawn_periodic(void)
{
    Status res;
    uint8_t tab[128];
    uint8_t count;
    uint32_t irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_set_periodic();
    timer_enable();

    for (count = 0; count < 5; ++count) {
        /* reeanble interrupt line (nvic unmasked)*/
        LOG("interrupt count %d wait", count);
        res = __sys_wait_for_event(EVENT_TYPE_IRQ, 0);
        copy_from_kernel(&tab[0], sizeof(exchange_event_t) + 4);
        ASSERT_EQ(res, STATUS_OK);
        uint32_t *IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
        ASSERT_EQ(*IRQn, irq);
        if (count < 4) {
            timer_enable_interrupt();
        }
    }
    /* waiting 2s, there should not have any more interrupts by now */
    res = __sys_wait_for_event(EVENT_TYPE_IRQ, 2000);
    ASSERT_EQ(res, STATUS_TIMEOUT);
}

void test_irq(void)
{
    Status res;

    TEST_SUITE_START("sys_irq");
    /* init timer for IRQ, no IT enabled yet */
    timer_map(&handle);
    timer_init();
    test_irq_spawn_one_it();
    test_irq_spawn_two_it();
    test_irq_spawn_periodic();
    timer_unmap(handle);
    TEST_SUITE_END("sys_irq");
    return;
}
