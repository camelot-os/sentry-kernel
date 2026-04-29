// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include "sha256_nist_parser.h"

#include <sentry/zlib/crypto.h>

#include <setjmp.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <cmocka.h>

#ifndef NIST_SHA256_VECTOR_DIR
#define NIST_SHA256_VECTOR_DIR "."
#endif

struct sha256_test_ctx {
    const char *label;
    size_t current_index;
    size_t executed;
};

static void to_hex(const uint8_t *in, size_t in_len, char *out, size_t out_len)
{
    static const char hex[] = "0123456789abcdef";
    size_t i;

    if (out_len == 0U) {
        return;
    }

    for (i = 0U; i < in_len && ((2U * i) + 1U) < out_len; i++) {
        out[2U * i] = hex[(in[i] >> 4) & 0x0F];
        out[(2U * i) + 1U] = hex[in[i] & 0x0F];
    }
    out[(2U * i < out_len) ? (2U * i) : (out_len - 1U)] = '\0';
}

static int run_sha256_vector(unsigned int len_bits,
                             const uint8_t *msg,
                             size_t msg_len,
                             const uint8_t md[32],
                             void *ctx)
{
    uint8_t out[SHA256_DIGEST_SIZE];
    int ret;
    struct sha256_test_ctx *test_ctx = (struct sha256_test_ctx *)ctx;
    char expected_hex[(SHA256_DIGEST_SIZE * 2U) + 1U];
    char got_hex[(SHA256_DIGEST_SIZE * 2U) + 1U];

    test_ctx->current_index += 1U;

    if ((test_ctx->current_index % 64U) == 0U) {
        printf("[NIST:%s] progress: vector %zu (len=%u bits)\n",
               test_ctx->label,
               test_ctx->current_index,
               len_bits);
    }

    ret = sha256(msg, (uint32_t)msg_len, out);
    if (ret != 0) {
        fprintf(stderr,
                "[NIST:%s] sha256() failed at vector=%zu len=%u bits msg_len=%zu ret=%d\n",
                test_ctx->label,
                test_ctx->current_index,
                len_bits,
                msg_len,
                ret);
        return -1;
    }

    if (memcmp(out, md, sizeof(out)) != 0) {
        to_hex(md, sizeof(out), expected_hex, sizeof(expected_hex));
        to_hex(out, sizeof(out), got_hex, sizeof(got_hex));

        fprintf(stderr,
                "[NIST:%s] digest mismatch at vector=%zu len=%u bits msg_len=%zu\n",
                test_ctx->label,
                test_ctx->current_index,
                len_bits,
                msg_len);
        fprintf(stderr, "[NIST:%s] expected=%s\n", test_ctx->label, expected_hex);
        fprintf(stderr, "[NIST:%s] got     =%s\n", test_ctx->label, got_hex);
        return -1;
    }

    test_ctx->executed += 1U;

    return 0;
}

static void test_sha256_nist_short_msg(void **state)
{
    struct sha256_test_ctx ctx = {
        .label = "ShortMsg",
        .current_index = 0U,
        .executed = 0U,
    };
    size_t parsed = 0U;
    int ret;
    char path[1024];

    (void)state;

    snprintf(path, sizeof(path), "%s/%s", NIST_SHA256_VECTOR_DIR, "SHA256ShortMsg.rsp");
    printf("[NIST:%s] starting vectors from %s\n", ctx.label, path);
    ret = sha256_nist_parse_file(path, run_sha256_vector, &ctx, &parsed);

    assert_int_equal(ret, 0);
    assert_int_equal(parsed, ctx.executed);
    assert_true(parsed > 0U);
    printf("[NIST:%s] done: validated %zu vectors\n", ctx.label, ctx.executed);
}

static void test_sha256_nist_long_msg(void **state)
{
    struct sha256_test_ctx ctx = {
        .label = "LongMsg",
        .current_index = 0U,
        .executed = 0U,
    };
    size_t parsed = 0U;
    int ret;
    char path[1024];

    (void)state;

    snprintf(path, sizeof(path), "%s/%s", NIST_SHA256_VECTOR_DIR, "SHA256LongMsg.rsp");
    printf("[NIST:%s] starting vectors from %s\n", ctx.label, path);
    ret = sha256_nist_parse_file(path, run_sha256_vector, &ctx, &parsed);

    assert_int_equal(ret, 0);
    assert_int_equal(parsed, ctx.executed);
    assert_true(parsed > 0U);
    printf("[NIST:%s] done: validated %zu vectors\n", ctx.label, ctx.executed);
}

int main(void)
{
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(test_sha256_nist_short_msg),
        cmocka_unit_test(test_sha256_nist_long_msg),
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
