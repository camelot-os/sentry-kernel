// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>
#include <sentry/zlib/crypto.h>
#include <sentry/zlib/math.h>
#include <sentry/zlib/sort.h>
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

void kernel_zlib(void)
{
    uint32_t res;
    char src[128];
    char dest[128];

    /* testing string.h API */
    /* defining volatile, unpredictible char value val to cover various use cases */
    volatile char val = 'a';
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

    /* memset */
    test_memset(0x0, 42);
    test_memset(0x42, 127);
    test_memset(0x0, 128);


    /* memcpy. Note: overlapping is forbidden by contract */
    sentry_memcpy(dest, src, 96);
    sentry_memcpy(dest, src, 31); /* not word aligned size */
    sentry_memcpy(&dest[20], dest, 12); /* non aligned */

#if 0
    /* testing entropy.h API */

    /*
     * PCG32() is a standard predictible sequence generator,
     * which random seed depends on the intial state value.
     * This part demonstrates that the sequence is respectful of the
     * PGC32 contract.
     */
    /*
       loop invariant 0 <= i <= 10;
       loop assigns res;
       loop variant 10 - i;
    */
    for (size_t i = 0; i < 10; ++i) {
        res = pcg32();
    }
    /* Calculate the CRC32 result of src, with initial masking of 0xffffffff */
    res = crc32((uint8_t*)src, len, 0xffffffff);
#endif
}
