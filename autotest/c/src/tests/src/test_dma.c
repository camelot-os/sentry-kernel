// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <string.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include <uapi/dma.h>
#include <shms-dt.h>
#include "test_dma.h"

static taskh_t myself;

#if CONFIG_HAS_GPDMA
static void test_dma_get_handle(dmah_t* d2mstreamh, dmah_t *m2mstreamh)
{
    Status res;
    TEST_START();
    res = __sys_get_dma_stream_handle(0x1);
    copy_from_kernel((uint8_t*)d2mstreamh, sizeof(dmah_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", *d2mstreamh);
    res = __sys_get_dma_stream_handle(0x2);
    copy_from_kernel((uint8_t*)m2mstreamh, sizeof(dmah_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", *m2mstreamh);
    TEST_END();
}

static void test_dma_get_handle_inval(void)
{
    Status res;
    dmah_t stream = 0;
    TEST_START();
    res = __sys_get_dma_stream_handle(0x42);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_start_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    res = __sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    res = __sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    /* assigned, should start */
    res = __sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    res = __sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_manipulate_stream_badhandle(void)
{
    Status res;
    TEST_START();
    res = __sys_dma_start_stream(0);
    ASSERT_EQ(res, STATUS_INVALID);
    res = __sys_dma_suspend_stream(0);
    ASSERT_EQ(res, STATUS_INVALID);
    res = __sys_dma_get_stream_status(0);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_get_stream_status(dmah_t stream)
{
    Status res;
    TEST_START();
    res = __sys_dma_get_stream_status(stream);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

static void test_dma_stop_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    res = __sys_dma_suspend_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_unassign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

static void test_dma_assign_unassign_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    res = __sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    res = __sys_dma_unassign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_unassign_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_start_n_wait_stream(dmah_t stream)
{
    Status res;
    shmh_t shm1;
    shm_infos_t shminfos1;
    shmh_t shm2;
    shm_infos_t shminfos2;
    uint32_t perms = 0;
    perms |= SHM_PERMISSION_WRITE;
    perms |= SHM_PERMISSION_MAP;
    int ret_builtin;
    TEST_START();
    res = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&myself, sizeof(taskh_t));
    // preparing shm1 with content
    res = __sys_get_shm_handle(shms[0].id);
    copy_from_kernel((uint8_t*)&shm1, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_set_credential(shm1, myself, perms);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_map_shm(shm1);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_get_infos(shm1);
    copy_from_kernel((uint8_t*)&shminfos1, sizeof(shm_infos_t));
    ASSERT_EQ(res, STATUS_OK);
    memset((void*)shminfos1.base, 0xa5, 0x100UL);
    // garbaging shm2
    res = __sys_get_shm_handle(shms[1].id);
    copy_from_kernel((uint8_t*)&shm2, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_set_credential(shm2, myself, perms);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_map_shm(shm2);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_get_infos(shm2);
    copy_from_kernel((uint8_t*)&shminfos2, sizeof(shm_infos_t));
    ASSERT_EQ(res, STATUS_OK);
    memset((void*)shminfos2.base, 0x42, 0x100UL);
    // start stream
    res = __sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    /* wait 50ms for DMA event, should rise in the meantime */
    res = __sys_wait_for_event(EVENT_TYPE_DMA, -1);
    ASSERT_EQ(res, STATUS_OK);
    // compare shm1 with shm2
    ret_builtin = memcmp((void*)shminfos1.base, (void*)shminfos2.base, 0x100);
    ASSERT_EQ((uint32_t)ret_builtin, 0);
    res = __sys_dma_suspend_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_unassign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

static void test_dma_get_info(dmah_t stream)
{
    Status res;
    gpdma_stream_cfg_t stream_info;
    shmh_t shm;
    shm_infos_t infos;
    TEST_START();
    res = __sys_get_shm_handle(shms[0].id);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_get_infos(shm);
    copy_from_kernel((uint8_t*)&infos, sizeof(shm_infos_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_get_dma_stream_handle(0x1);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_dma_get_stream_info(stream);
    copy_from_kernel((uint8_t*)&stream_info, sizeof(gpdma_stream_cfg_t));
    ASSERT_EQ(res, STATUS_OK);
    ASSERT_EQ((uint32_t)stream_info.stream, 112);
    ASSERT_EQ((uint32_t)stream_info.channel, 1);
    ASSERT_EQ((uint32_t)stream_info.controller, 0);
    ASSERT_EQ((uint32_t)stream_info.transfer_type, GPDMA_TRANSFER_DEVICE_TO_MEMORY);
    ASSERT_EQ((uint32_t)stream_info.transfer_len, 42UL);
    ASSERT_EQ((uint32_t)stream_info.source, 0);
    /* target should be SHM base addr */
    ASSERT_EQ((uint32_t)stream_info.dest, infos.base);
    ASSERT_EQ((uint32_t)stream_info.circular_source, 1);
    ASSERT_EQ((uint32_t)stream_info.circular_dest, 0);
    ASSERT_EQ((uint32_t)stream_info.priority, GPDMA_PRIORITY_MEDIUM);
    TEST_END();
}

#endif

void test_dma(void)
{
    dmah_t d2mstream = 0;
    dmah_t m2mstream = 0;
    Status res;
    TEST_SUITE_START("sys_dma");
#if CONFIG_HAS_GPDMA
    test_dma_get_handle(&d2mstream, &m2mstream);
    test_dma_get_handle_inval();
    test_dma_get_info(d2mstream);
    test_dma_manipulate_stream_badhandle();
    test_dma_assign_unassign_stream(m2mstream);
    test_dma_start_n_wait_stream(m2mstream);
    test_dma_start_stream(m2mstream);
    test_dma_get_stream_status(m2mstream);
    test_dma_stop_stream(m2mstream);
#endif
    TEST_SUITE_END("sys_dma");
}
