// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include <uapi/types.h>
#include "test_ipc.h"

void test_ipc_send_toobig(void)
{
    Status ret;
    taskh_t handle = 0;
    uint8_t len = CONFIG_SVC_EXCHANGE_AREA_LEN+1;
    ret = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&handle, sizeof(taskh_t));
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    LOG("sending invalid IPC size %lu", (uint32_t)len);
    ret = __sys_send_ipc(handle, len);
    ASSERT_EQ(ret, STATUS_INVALID);
    len = 255;
    LOG("sending invalid IPC size %lu", (uint32_t)len);
    ret = __sys_send_ipc(handle, len);
    ASSERT_EQ(ret, STATUS_INVALID);
    TEST_END();
}

void test_ipc_send_invalidtarget(void)
{
    Status ret;
    TEST_START();
    LOG("sending IPC to invalid target");
    ret = __sys_send_ipc(0xdead1001UL, 20);
    ASSERT_EQ(ret, STATUS_INVALID);
    TEST_END();
}

void test_ipc_sendrecv(void)
{
    static const char *msg = "hello it's autotest";
    Status ret;
    taskh_t handle = 0;
    uint8_t data[CONFIG_SVC_EXCHANGE_AREA_LEN] = {0};
    int32_t timeout = 100L; /* milisecond timeout */
    exchange_event_t *header;

    ret = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&handle, sizeof(taskh_t));
    LOG("handle is %lx", handle);
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    LOG("sending IPC to myself");
    copy_to_kernel(msg, 20);
    ret = __sys_send_ipc(handle, 20);
    ret = __sys_wait_for_event(EVENT_TYPE_IPC, timeout);
    copy_from_kernel(data, 20+sizeof(exchange_event_t));
    header = (exchange_event_t*)&data[0];
    uint32_t source = header->source;
    char *content = (char*)&header->data[0];
    LOG("%x:%u:%x:src=%lx %s",
        header->type,
        header->length,
        header->magic,
        header->source,
        content);
    ASSERT_EQ(ret, STATUS_OK);
    TEST_END();
}

void test_ipc_deadlock(void)
{
    static const char *msg = "hello it's autotest";
    Status ret;
    taskh_t handle = 0;
    uint8_t data[CONFIG_SVC_EXCHANGE_AREA_LEN] = {0};
    int32_t timeout = 100L; /* milisecond timeout */
    exchange_event_t *header;

    ret = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&handle, sizeof(taskh_t));
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    LOG("sending IPC to myself");
    copy_to_kernel(msg, 20);
    ret = __sys_send_ipc(handle, 20);
    ASSERT_EQ(ret, STATUS_OK);
    LOG("sending another IPC, should lead to STATUS_DEADLK");
    ret = __sys_send_ipc(handle, 20);
    ASSERT_EQ(ret, STATUS_DEADLK);
    TEST_END();
}

void test_ipc(void)
{
    TEST_SUITE_START("sys_ipc");

    test_ipc_sendrecv();
    test_ipc_send_invalidtarget();
    test_ipc_send_toobig();
    test_ipc_deadlock();

    TEST_SUITE_END("sys_ipc");
}
