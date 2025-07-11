// SPDX-FileCopyrightText: 2025 Camelot OSS Team
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <setjmp.h>
#include <cmocka.h>

#include <sentry/arch/asm-cortex-m/layout.h>
#include <bsp/drivers/exti/exti.h>
#include <sentry/ktypes.h>
#include <garbage.h>
#include "stm32-exti-dt.h"

static void test_probe(void **state) {
    assert_int_equal(exti_probe(), K_STATUS_OKAY);
}

static void test_exti_interrupts(void **state) {
    for (int n = 0; n != 127; ++n) {
        uint8_t val;
        get_garbage(&val);
        kstatus_t res;
        res = exti_unmask_interrupt(val);
        if (val <= EXTI_NUM_EVENTS) {
            assert_int_equal(res, K_STATUS_OKAY);
        } else {
            assert_int_equal(res, K_ERROR_INVPARAM);
        }
    };
    for (int n = 0; n != 127; ++n) {
        uint8_t val;
        get_garbage(&val);
        kstatus_t res;
        res = exti_mask_interrupt(val);
        if (val <= EXTI_NUM_EVENTS) {
            assert_int_equal(res, K_STATUS_OKAY);
        } else {
            assert_int_equal(res, K_ERROR_INVPARAM);
        }
    };
}

int main(void) {
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(test_probe),
        cmocka_unit_test(test_exti_interrupts),
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
