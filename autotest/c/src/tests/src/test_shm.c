// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include "test_shm.h"

/**
 * Note: in autotest-based DTS, the following SHM are defined
 * (see local dts example files)
 */
#include <shms-dt.h>

static_assert(SHM_LIST_SIZE == 4, "invalid autotest SHM list");

#define SHM_MAP_DMAPOOL shms[0].id
#define SHM_MAP_NODMAPOOL shms[2].id
#define SHM_NOMAP_DMAPOOL shms[3].id

/* TODO: use generated instead */
#define SHM_MAP_DMAPOOL_BASEADDR shms[0].baseaddr
#define SHM_MAP_DMAPOOL_SIZE shms[0].size

static taskh_t myself;
static taskh_t idle;

void test_shm_handle(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_get_shm_handle(SHM_NOMAP_DMAPOOL);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_get_shm_handle(SHM_MAP_NODMAPOOL);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_get_shm_handle(0x42);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_shm_unmap_notmapped(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_unmap_shm(shm);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_shm_invalidmap(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    shm += 42;
    res = __sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_shm_mapdenied(void) {
    Status res;
    shmh_t shm;
    uint32_t perms = 0;
    perms |= SHM_PERMISSION_WRITE;
    perms |= SHM_PERMISSION_MAP;
    TEST_START();
    res = __sys_get_shm_handle(SHM_NOMAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_set_credential(shm, myself, perms);
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_DENIED);
    TEST_END();
}

void test_shm_infos(void) {
    Status res;
    shmh_t shm;
    shm_infos_t infos;
    TEST_START();
    res = __sys_get_shm_handle(shms[0].id);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_shm_get_infos(shm);
    copy_from_kernel((uint8_t*)&infos, sizeof(shm_infos_t));

    ASSERT_EQ(res, STATUS_OK);
    ASSERT_EQ(infos.label, shms[0].id);
    ASSERT_EQ(infos.handle, shm);
    ASSERT_EQ((uint32_t)infos.base, (uint32_t)shms[0].baseaddr);
    ASSERT_EQ((uint32_t)infos.len, (uint32_t)shms[0].size);

    TEST_END();
}

void test_shm_creds_on_mapped(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    /* get own handle first */
    res = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&myself, sizeof(taskh_t));
    /* get shm handle then */
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    uint32_t perms = (SHM_PERMISSION_MAP | SHM_PERMISSION_WRITE);
    res = __sys_shm_set_credential(shm, myself, perms);
    ASSERT_EQ(res, STATUS_OK);
    /* map SHM */
    res = __sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_OK);
    /* try to set creds on mapped SHM */
    perms = (SHM_PERMISSION_WRITE);
    res = __sys_shm_set_credential(shm, myself, perms);
    ASSERT_EQ(res, STATUS_BUSY);
    /* unmap SHM */
    res = __sys_unmap_shm(shm);
    ASSERT_EQ(res, STATUS_OK);
    /* set creds after unmap */
    res = __sys_shm_set_credential(shm, myself, perms);
    ASSERT_EQ(res, STATUS_OK);

    TEST_END();
}

void test_shm_allows_idle(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    /* get idle handle first */
    res = __sys_get_process_handle(0xcafeUL);
    copy_from_kernel((uint8_t*)&idle, sizeof(taskh_t));
    /* get shm handle then */
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    uint32_t perms = SHM_PERMISSION_TRANSFER;
    res = __sys_shm_set_credential(shm, idle, perms);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

void test_shm_map_unmappable(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    /* get own handle first */
    res = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&myself, sizeof(taskh_t));
    /* get shm handle then */
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", shm);
    /* give full write to myself */
    uint32_t perms = 0;
    perms |= SHM_PERMISSION_WRITE;
    res = __sys_shm_set_credential(shm, myself, perms);
    LOG("creds set");
    ASSERT_EQ(res, STATUS_OK);
    /* map SHM, should fail as creds not mappable */
    res = __sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_DENIED);
    TEST_END();
}

void test_shm_mapunmap(void) {
    Status res;
    shmh_t shm;
    TEST_START();
    /* get own handle first */
    res = __sys_get_process_handle(0xbabeUL);
    copy_from_kernel((uint8_t*)&myself, sizeof(taskh_t));
    /* get shm handle then */
    res = __sys_get_shm_handle(SHM_MAP_DMAPOOL);
    copy_from_kernel((uint8_t*)&shm, sizeof(shmh_t));
    LOG("handle is %lx", shm);
    ASSERT_EQ(res, STATUS_OK);
    /* give full write to myself */
    uint32_t perms = 0;
    perms |= SHM_PERMISSION_WRITE;
    perms |= SHM_PERMISSION_MAP;
    res = __sys_shm_set_credential(shm, myself, perms);
    ASSERT_EQ(res, STATUS_OK);
    LOG("creds set");
    /* map SHM */
    res = __sys_map_shm(shm);
    ASSERT_EQ(res, STATUS_OK);
    if (res != STATUS_OK) {
        goto end;
    }

    uint32_t* shmptr = (uint32_t*)SHM_MAP_DMAPOOL_BASEADDR;
    LOG("shm mapped, checking read/write");
    for (uint8_t offset = 0; offset < 12*sizeof(uint32_t); offset += 4) {
        *shmptr = offset;
        shmptr++;
    }
    LOG("unmapping");
    res = __sys_unmap_shm(shm);
    ASSERT_EQ(res, STATUS_OK);
end:
    TEST_END();
}

void test_shm(void) {
    TEST_SUITE_START("sys_map_shm");
    test_shm_handle();
    test_shm_invalidmap();
    test_shm_unmap_notmapped();
    test_shm_mapunmap();
    test_shm_map_unmappable();
    test_shm_mapdenied();
    test_shm_creds_on_mapped();
    test_shm_infos();
    test_shm_allows_idle();
    TEST_SUITE_END("sys_map_shm");
}
