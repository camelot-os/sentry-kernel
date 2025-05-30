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
#if 0
    /* Calculate the CRC32 result of src, with initial masking of 0xffffffff */
    res = crc32((uint8_t*)src, len, 0xffffffff);
#endif
}
