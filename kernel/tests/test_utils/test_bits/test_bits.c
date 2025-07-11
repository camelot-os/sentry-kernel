// SPDX-FileCopyrightText: 2025 Camelot OSS Team
// SPDX-License-Identifier: Apache-2.0


#include <sentry/bits.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <setjmp.h>
#include <cmocka.h>

static void test_bits(void **state __attribute__((unused))) {
    assert_int_equal(BIT(0), 0x00000001);
    assert_int_equal(BIT(1), 0x00000002);
    assert_int_equal(BIT(2), 0x00000004);
    assert_int_equal(BIT(3), 0x00000008);
    assert_int_equal(BIT(4), 0x00000010);
    assert_int_equal(BIT(5), 0x00000020);
    assert_int_equal(BIT(6), 0x00000040);
    assert_int_equal(BIT(7), 0x00000080);
    assert_int_equal(BIT(8), 0x00000100);
    assert_int_equal(BIT(9), 0x00000200);
    assert_int_equal(BIT(10), 0x00000400);
    assert_int_equal(BIT(11), 0x00000800);
    assert_int_equal(BIT(12), 0x00001000);
    assert_int_equal(BIT(13), 0x00002000);
    assert_int_equal(BIT(14), 0x00004000);
    assert_int_equal(BIT(15), 0x00008000);
    assert_int_equal(BIT(16), 0x00010000);
    assert_int_equal(BIT(17), 0x00020000);
    assert_int_equal(BIT(18), 0x00040000);
    assert_int_equal(BIT(19), 0x00080000);
    assert_int_equal(BIT(20), 0x00100000);
    assert_int_equal(BIT(21), 0x00200000);
    assert_int_equal(BIT(22), 0x00400000);
    assert_int_equal(BIT(23), 0x00800000);
    assert_int_equal(BIT(24), 0x01000000);
    assert_int_equal(BIT(25), 0x02000000);
    assert_int_equal(BIT(26), 0x04000000);
    assert_int_equal(BIT(27), 0x08000000);
    assert_int_equal(BIT(28), 0x10000000);
    assert_int_equal(BIT(29), 0x20000000);
    assert_int_equal(BIT(30), 0x40000000);
    assert_int_equal(BIT(31), 0x80000000);
}

static void test_bitfields_mask(void **state __attribute__((unused))) {
    assert_int_equal(BITFIELD_MASK(0, 0), 0x1);
    assert_int_equal(BITFIELD_MASK(7, 7), 0x80);
    assert_int_equal(BITFIELD_MASK(8, 8), 0x100);
    assert_int_equal(BITFIELD_MASK(15, 15), 0x8000);
    assert_int_equal(BITFIELD_MASK(16, 16), 0x10000);
    assert_int_equal(BITFIELD_MASK(23, 23), 0x800000);
    assert_int_equal(BITFIELD_MASK(24, 24), 0x1000000);
    assert_int_equal(BITFIELD_MASK(31, 31), 0x80000000);
}

static void test_rngbitmasks(void **state __attribute__((unused))) {
    assert_int_equal(BITFIELD_MASK(12, 0), 0x1fff);
    assert_int_equal(BITFIELD_MASK(24, 18), 0x1fc0000);
    assert_int_equal(BITFIELD_MASK(31, 9), 0xfffffe00);
    assert_int_equal(BITFIELD_MASK(22, 10), 0x007ffc00);
}

static void test_fullmask(void **test __attribute__((unused))) {
    assert_int_equal(BITFIELD_MASK(31, 0), 0xffffffff);
}

static void test_bitshift(void **test __attribute__((unused))) {
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(0)), 0);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(1)), 1);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(2)), 2);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(3)), 3);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(4)), 4);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(5)), 5);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(6)), 6);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(7)), 7);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(8)), 8);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(9)), 9);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(10)), 10);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(11)), 11);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(12)), 12);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(13)), 13);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(14)), 14);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(15)), 15);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(16)), 16);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(17)), 17);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(18)), 18);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(19)), 19);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(20)), 20);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(21)), 21);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(22)), 22);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(23)), 23);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(24)), 24);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(25)), 25);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(26)), 26);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(27)), 27);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(28)), 28);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(29)), 29);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(30)), 30);
    assert_int_equal(__BITSHIFT_FROM_MASK(BIT(31)), 31);
}

static void test_shift_from_mask(void **state __attribute__((unused))) {
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(0, 0)), 0);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(7, 7)), 7);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(8, 8)), 8);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(15, 15)), 15);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(16, 16)), 16);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(23, 23)), 23);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(24, 24)), 24);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(31, 31)), 31);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(12, 0)), 0);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(24, 18)), 18);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(31, 9)), 9);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(22, 10)), 10);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(31, 0)), 0);
    assert_int_equal(__BITSHIFT_FROM_MASK(BITFIELD_MASK(31, 0)), 0);
}

int main(void) {
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(test_bits),
        cmocka_unit_test(test_bitshift),
        cmocka_unit_test(test_bitfields_mask),
        cmocka_unit_test(test_shift_from_mask),
        cmocka_unit_test(test_rngbitmasks),
        cmocka_unit_test(test_fullmask),
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
