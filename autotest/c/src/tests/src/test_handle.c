// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include "test_ipc.h"

typedef struct __attribute__((packed)) ktaskh  {
    uint32_t rerun : 20;
    uint32_t id : 8;
    uint32_t family : 3;
} ktaskh_t;

void test_gethandle(void)
{
    Status ret;
    taskh_t handle = 0;
    ktaskh_t khandle;

    TEST_START();
    /* clear svcexchange first */
    copy_to_kernel((uint8_t*)&handle, sizeof(handle));
    copy_from_kernel((uint8_t*)&handle, sizeof(handle));
    ASSERT_EQ(handle, 0);
    ret = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&handle, sizeof(taskh_t));
    ASSERT_EQ(ret, STATUS_OK);
    LOG("received handle: %lx", handle);
    __builtin_memcpy(&khandle, &handle, sizeof(ktaskh_t));
    LOG("handle rerun = %lx", (uint32_t)khandle.rerun);
    LOG("handle id = %lx", (uint32_t)khandle.id);
    LOG("handle family = %lx", (uint32_t)khandle.family);
    TEST_END();
}

void test_handle(void)
{
    TEST_SUITE_START("sys_get_handle");

    test_gethandle();

    TEST_SUITE_END("sys_get_handle");
}
