// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include <uapi/types.h>
#include "test_ipc.h"


void test_signal_sendrecv(void)
{
    Status ret;
    taskh_t handle = 0;
    int32_t timeout = 20L;
    uint8_t data[CONFIG_SVC_EXCHANGE_AREA_LEN] = {0};
    exchange_event_t *header;

    ret = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&handle, sizeof(taskh_t));
    LOG("handle is %lx", handle);
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    Signal sig = SIGNAL_ABORT;
    for (sig = SIGNAL_ABORT; sig <= SIGNAL_USR2; ++sig) {
        LOG("sending signal %u to myself", sig);
        ret = __sys_send_signal(handle, sig);
        ret = __sys_wait_for_event(EVENT_TYPE_SIGNAL, timeout);
        copy_from_kernel(data, 4+sizeof(exchange_event_t));
        header = (exchange_event_t*)&data[0];
        uint32_t* content = (uint32_t*)&header->data[0];
        LOG("%x:%u:%x:src=%lx signal=%lu",
            header->type,
            header->length,
            header->magic,
            header->source,
            *content);

        ASSERT_EQ(ret, STATUS_OK);
        ASSERT_EQ(*content, sig);
    }
    TEST_END();
}

void test_signal(void)
{
    TEST_SUITE_START("sys_signal");

    test_signal_sendrecv();

    TEST_SUITE_END("sys_signal");
}
