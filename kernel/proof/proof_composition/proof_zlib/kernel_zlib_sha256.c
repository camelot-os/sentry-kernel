// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>
#include <sentry/zlib/crypto.h>

/*@ assigns \nothing; */
void kernel_zlib(void)
{
    int ret;
    uint8_t input[256];
    uint8_t output[SHA256_DIGEST_SIZE];
    sha256_context ctx;
    volatile uint8_t val = 0;

    /* initializing input with garbaged (unpredictable) values */
    /*@
      loop invariant 0 <= i <= 256;
      loop assigns i, input[0 .. 255];
      loop variant 256 - i;
     */
    for (size_t i = 0; i < 256; ++i) {
        input[i] = val;
    }

    /* testing sha256_init */
    ret = sha256_init(&ctx);
    /*@ assert ret == 0; */

    /* testing sha256_update with various input sizes */
    ret = sha256_update(&ctx, input, 0);
    /*@ assert ret == 0; */

    ret = sha256_update(&ctx, input, 64);
    /*@ assert ret == 0; */

    ret = sha256_update(&ctx, input, 128);
    /*@ assert ret == 0; */

    ret = sha256_update(&ctx, input, 256);
    /*@ assert ret == 0; */

    /* testing sha256_final */
    ret = sha256_final(&ctx, output);
    /*@ assert ret == 0; */

    /* reinitialize for scattered test */
    ret = sha256_init(&ctx);
    /*@ assert ret == 0; */

    /* testing sha256_scattered with multiple input blocks */
    const uint8_t *inputs[4] = {
        input,
        input + 64,
        input + 128,
        NULL  /* sentinelle terminating the array */
    };
    const uint32_t ilens[4] = {
        64,
        64,
        128,
        0  /* unused but necessary for array alignment */
    };

    ret = sha256_scattered(inputs, ilens, output);
    /*@ assert ret == 0; */

    /* testing sha256 with various input sizes */
    ret = sha256(NULL, 0, output);
    /*@ assert ret == 0; */

    ret = sha256(input, 64, output);
    /*@ assert ret == 0; */

    ret = sha256(input, 128, output);
    /*@ assert ret == 0; */

    ret = sha256(input, 256, output);
    /*@ assert ret == 0; */
}
