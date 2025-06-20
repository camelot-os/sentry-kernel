// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>
#include <sentry/zlib/string.h>

/** TODO: expose sentry_xxx of string.h instead of using externs here */

/**
 * NOTE: in non-proof mode, these symbols are aliased to corresponding compiler
 * builtins, and as such resolvable by the compiler.
 * Nonetheless, we want here to check their implementation, and thus be able
 * to explicitly call them.
 * These symbols are a part of the Sentry zlib
 */
void   *sentry_memcpy(void * restrict dest, const void* restrict src, size_t n);
void   *sentry_memset(void *s, int c, unsigned int n);
size_t sentry_strnlen(const char *s, size_t maxlen);

/*@ assigns \nothing; */
static inline void test_memset(int c, unsigned int n)
{
    uint8_t s[n];
    sentry_memset(NULL, c, n);
    sentry_memset(s, c, n);
}

/*@ assigns \nothing; */
void kernel_zlib(void)
{
    uint32_t res;
    char src[128];
    char dest[128];

    /* testing string.h API */
    /* defining volatile, unpredictible char value val to cover various use cases */
    volatile char val = 'a';
    /* initilizing src with garbaged (unpredictable) yet valid chars */
    /*@
      loop invariant 0 <= i <= 128;
      loop assigns i, src[0 .. 127];
      loop variant 128 - i;
     */
    for (size_t i = 0; i < 128; ++i) {
        src[i] = val;
    }
    /* at list finishing with null-char at the end (valid ISO C string) */
    src[127] = '\0';
    /*@ assert \initialized(src+(0..127)); */
    /*
     * formal proofness imposes that the input string is valid in all calls,
     * meaning ASCII char + null termination.
     * any call to strnlen() in the kernel must respects this contract or the
     * proof will fail.
     * NOTE: the null check is kept as dead code (allowed) that include
     * an assert(false).
     */

    size_t len = sentry_strnlen(src, 128);
    len = sentry_strnlen(NULL, 128);
    len = sentry_strnlen(src, 1);
    len = sentry_strnlen(src, 0);

    /* memset */
    test_memset(0x0, 42);
    test_memset(0x42, 127);
    test_memset(0x0, 128);


    /* memcpy. Note: overlapping is forbidden by contract */
    sentry_memcpy(NULL, src, 96);
    sentry_memcpy(NULL, NULL, 96);
    sentry_memcpy(dest, NULL, 96);
    sentry_memcpy(dest, src, 96);
    sentry_memcpy(dest, src, 0);
    sentry_memcpy(dest, src, 31); /* not word aligned size */
    sentry_memcpy(&dest[1], src, 12); /* non word-aligned memraeas */


}
