// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>
#include <sentry/zlib/crypto.h>

/*@ assigns \nothing; */
void kernel_zlib(void)
{
    uint32_t res;
    uint8_t src[128];
    volatile uint8_t val = 0;
    /* initilizing src with garbaged (unpredictable) values */
    /*@
      loop invariant 0 <= i <= 128;
      loop assigns i, src[0 .. 127];
      loop variant 128 - i;
     */
    for (size_t i = 0; i < 128; ++i) {
        src[i] = val;
    }
    /* testing entropy.h API */

    // call with default, no seeding
    res = pcg32();
    // seeding PGC32 with new state and inc values
    pcg32_seed(0x123456789abcdef0ULL, 0x0fedcba987654321ULL);
    /*
     * PCG32() is a standard predictible sequence generator,
     * which random seed depends on the intial state value.
     * This part demonstrates that the sequence is respectful of the
     * PGC32 contract.
     */
    uint32_t old_res = res;
    res = pcg32();
    /*@ assert old_res != res; */
    /* Calculate the CRC32 result of src, with initial masking of 0xffffffff */
    res = crc32(NULL, 128, 0xffffffff);
    res = crc32(src, 128, 0xffffffff);
    res = crc32(src, 0, 0xffffffff);
}
