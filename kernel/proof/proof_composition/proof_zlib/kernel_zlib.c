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

void kernel_zlib(void)
{
    uint32_t res;
    char src[128];
    char dest[128];

    /*@
      loop invariant 0 <= i <= 128;
      loop invariant \forall integer k; 0 <= k < i ==> src[k] == Frama_C_entropy_source_u8;
      loop assigns i, src[0 .. 127];
      loop variant 128 - i;
     */
    for (uint8_t i = 0; i < 128; ++i) {
        dest[i] = Frama_C_entropy_source_u8;
    }
    size_t len = sentry_strnlen(src, 128);
    Frama_C_memset(dest, 0, 128);
    sentry_memcpy(dest, src, 128);
    Frama_C_memset(dest, 0, 128);
    sentry_memcpy(dest, src, 31); /* not word aligned size */
    Frama_C_memset(dest, 0, 128);
    /* overlapped regions, in both order */
    sentry_memcpy(&dest[0], &dest[20], 42);
    sentry_memcpy(&dest[20], &dest[0], 42);
}
