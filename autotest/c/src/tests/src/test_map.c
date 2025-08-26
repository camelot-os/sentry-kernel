// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <test_log.h>
#include <test_assert.h>
#include <uapi/uapi.h>
#include <devices-dt.h>
#include "test_gpio.h"

#if DEVICE_LIST_SIZE > 0

void test_map_unmap_notmapped(void) {
    Status res;
    devh_t dev;
    TEST_START();
    res = __sys_get_device_handle((uint8_t)devices[DEV_ID_I2C1].id);
    copy_from_kernel((uint8_t*)&dev, sizeof(devh_t));
    ASSERT_EQ(res, STATUS_OK);
    res = __sys_unmap_dev(dev);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_map_invalidmap(void) {
    Status res;
    devh_t dev;
    TEST_START();
    res = __sys_get_device_handle((uint8_t)devices[DEV_ID_I2C1].id);
    copy_from_kernel((uint8_t*)&dev, sizeof(devh_t));
    ASSERT_EQ(res, STATUS_OK);
    dev += 42;
    res = __sys_map_dev(dev);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_map_mapunmap(void) {
    Status res;
    devh_t dev;

    TEST_START();
    res = __sys_get_device_handle((uint8_t)devices[DEV_ID_I2C1].id);
    copy_from_kernel((uint8_t*)&dev, sizeof(devh_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", dev);
    res = __sys_map_dev(dev);
    ASSERT_EQ(res, STATUS_OK);
    if (res == STATUS_OK) {
        LOG("device mapped, checking registers");
        for (uint8_t offset = 0; offset < 12*sizeof(uint32_t); offset += 4) {
#ifdef CONFIG_ARCH_MCU_STM32U5A5
            /* checking effective registers reset values. Must match the datasheet */
            if (offset != 6*sizeof(uint32_t)) {
                ASSERT_EQ((uint32_t)*(uint32_t*)(devices[DEV_ID_I2C1].baseaddr + offset), 0x0);
            } else {
                ASSERT_EQ((uint32_t)*(uint32_t*)(devices[DEV_ID_I2C1].baseaddr + offset), 0x1);
            }
#endif
        }
    }
    LOG("unmapping");
    res = __sys_unmap_dev(dev);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}
#endif


void test_map(void) {
#if DEVICE_LIST_SIZE > 0
    TEST_SUITE_START("sys_map");
    test_map_mapunmap();
    test_map_invalidmap();
    test_map_unmap_notmapped();
    TEST_SUITE_END("sys_map");
#endif
}
