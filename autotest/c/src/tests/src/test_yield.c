// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include "test_yield.h"

void test_yield(void)
{
    TEST_SUITE_START("sys_yield");
    Status ret;
    TEST_START();
    LOG("yielding...");
    ret = __sys_sched_yield();
    ASSERT_EQ(ret, STATUS_OK);
    LOG("yielding...");
    ret = __sys_sched_yield();
    ASSERT_EQ(ret, STATUS_OK);
    LOG("yielding...");
    ret = __sys_sched_yield();
    ASSERT_EQ(ret, STATUS_OK);
    TEST_END();
    TEST_SUITE_END("sys_yield");
}
