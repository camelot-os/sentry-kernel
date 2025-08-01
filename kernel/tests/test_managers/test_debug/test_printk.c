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
#include <garbage.h>
#include <sentry/ktypes.h>
#include <sentry/managers/debug.h>
#include <cmocka.h>

/* FIXME: SEE printk lexer file, still hard-coded by now */
#define BUF_MAX 128UL

static char model[BUF_MAX];

/**
 * @brief auto-compare to previously set model string
 *
 * This requires that testing printk() kernel call must be done using the following state automaton
 * - fulfill the model with the snprintf() stdio API
 * - call printk() with the very same format string. This call will go down to this function that
 *   will compare to the previously set model
 */
kstatus_t debug_rawlog(const uint8_t *logbuf, size_t len __attribute__((unused))) {
    assert_string_equal(logbuf, model);
    return K_STATUS_OKAY;
}

void test_percent_char(void**state __attribute__((unused))) {
    snprintf(model, BUF_MAX, "%%");
    printk("%%");
}

void test_poiners(void**state __attribute__((unused))) {
    snprintf(model, BUF_MAX, "%p", test_poiners);
    printk("%p", test_poiners);
}

void test_unsigned(void**state __attribute__((unused))) {
    unsigned u;
    unsigned long ul;
    unsigned long long ull;

    get_garbage(&u);
    snprintf(model, BUF_MAX, "%u", u);
    printk("%u", u);
    get_garbage(&ul);
    snprintf(model, BUF_MAX, "%lu", ul);
    printk("%lu", ul);
    get_garbage(&ull);
    snprintf(model, BUF_MAX, "%llu", ull);
    printk("%llu", ull);
}

void test_hexa(void**state __attribute__((unused))) {
    unsigned u;
    unsigned long ul;

    get_garbage(&u);
    snprintf(model, BUF_MAX, "%x", u);
    printk("%x", u);
    get_garbage(&ul);
    snprintf(model, BUF_MAX, "%lx", ul);
    printk("%lx", ul);
    /* NOTE: by now, the kernel printk() do not support '%llx' */
}

void test_int_format(void**state __attribute__((unused))) {
    unsigned long ul;
    unsigned u;
    int i;


    for (uint8_t count = 0; count < 127; ++count) {
        get_garbage(&i);
        snprintf(model, BUF_MAX, "%05i", i);
        printk("%05i", i);

#if 0
        long d;
        /** FIXME: ld is not supported in printk() implementation */
        get_garbage(&d);
        snprintf(model, BUF_MAX, "%05ld", d);
        printk("%05ld", d);
#endif

        get_garbage(&u);
        snprintf(model, BUF_MAX, "%05u", u);
        printk("%05u", u);

        get_garbage(&ul);
        snprintf(model, BUF_MAX, "%05lu", ul);
        printk("%05lu", ul);
    }

}

void test_str(void**state __attribute__((unused))) {
    char *none = NULL;
    const char * basic = "my taylor is rich!";
    const char * complex = "I have %d eggs in my pocket\n";

    snprintf(model, BUF_MAX, "%s", none);
    printk("%s", none);

    snprintf(model, BUF_MAX, basic);
    printk(basic);

    snprintf(model, BUF_MAX, complex, 12);
    printk(complex, 12);
}

int main(void) {
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(test_percent_char),
        cmocka_unit_test(test_poiners),
        cmocka_unit_test(test_unsigned),
        cmocka_unit_test(test_hexa),
        cmocka_unit_test(test_int_format),
        cmocka_unit_test(test_str),
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
