// SPDX-FileCopyrightText: 2025 Camelot OSS Team
// SPDX-License-Identifier: Apache-2.0

#include <sentry/io.h>
#include <garbage.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <setjmp.h>
#include <cmocka.h>


static void test_io_write32(void **state __attribute__((unused))) {

    uint32_t reg_value_random;
    get_garbage(&reg_value_random);
    uint32_t reg;


    for (int n = 0; n != 255; ++n) {
            uint32_t res;
            iowrite((size_t)&reg, reg_value_random);
            res = ioread32((size_t)&reg);
            assert_int_equal(reg_value_random, res);
    };
}

static void test_io_write16(void **state __attribute__((unused))) {

    uint16_t reg_value_random;
    get_garbage(&reg_value_random);
    uint16_t reg;


    for (int n = 0; n != 255; ++n) {
            uint16_t res;
            iowrite((size_t)&reg, reg_value_random);
            res = ioread16((size_t)&reg);
            assert_int_equal(reg_value_random, res);
    };
}

static void test_io_write8(void **state __attribute__((unused))) {

    uint8_t reg_value_random;
    get_garbage(&reg_value_random);
    uint8_t reg;


    for (int n = 0; n != 255; ++n) {
            uint8_t res;
            iowrite((size_t)&reg, reg_value_random);
            res = ioread8((size_t)&reg);
            assert_int_equal(reg_value_random, res);
    };
}

int main(void) {
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(test_io_write32),
        cmocka_unit_test(test_io_write16),
        cmocka_unit_test(test_io_write8),
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
