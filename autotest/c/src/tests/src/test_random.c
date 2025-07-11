// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include "test_random.h"



void test_random_sequence(void)
{
    Status ret;
    uint32_t rng;
    TEST_START();
    LOG("get back random value from KRNG");
    for (uint32_t idx = 0; idx < 5; ++idx) {
        ret = __sys_get_random();
        copy_from_kernel((uint8_t*)&rng, sizeof(uint32_t));
        ASSERT_EQ(ret, STATUS_OK);
        LOG("rng retreived: 0x%lx", rng);
    }
    TEST_END();
}

void test_random_duration(void)
{
    uint64_t start, stop;
    uint32_t rng, idx;
    __sys_sched_yield();
    __sys_get_cycle(PRECISION_MICROSECONDS);
    copy_from_kernel((uint8_t*)&start, sizeof(uint64_t));
    for (idx = 0; idx <= 1000; ++idx) {
        __sys_get_random();
        copy_from_kernel((uint8_t*)&rng, sizeof(uint32_t));
    }
    __sys_get_cycle(PRECISION_MICROSECONDS);
    copy_from_kernel((uint8_t*)&stop, sizeof(uint64_t));
    LOG("average get_random+copy cost: %lu", (uint32_t)((stop - start) / idx));
}

void test_random(void)
{
    TEST_SUITE_START("sys_get_random");

    test_random_sequence();
    test_random_duration();

    TEST_SUITE_END("sys_get_random");
}
