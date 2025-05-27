// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <sentry/zlib/crypto.h>

#define KBYTE 1024
#define MBYTE 1048576
#define GBYTE 1073741824

/*
 * Basic PCG32 implementation
 * TODO: to be reviewed by Patrice, fixed with RNG source
 */
static const uint64_t N = 6364136223846793005ULL;
static uint64_t state = 0x853c49e6748fea9bULL;
static uint64_t inc = 0xda3e39cb94b95bdbULL;


/*
 * Get back a new value of the PCG32 deterministic sequence based on
 * a given seed
 */
/*@
   requires \true;
   assigns state;

   // state predictible upgrade
   ensures state == \old(state) * 6364136223846793005ULL + 0xda3e39cb94b95bdbULL;
   // TODO framlly defined result formula
   ensures \result == ((\old(state) / (1ULL << 18)) ^ \old(state)) / (1ULL << 27) / (\old(state) / (1ULL << 59)) +
                     (((\old(state) / (1ULL << 18)) ^ \old(state)) / (1ULL << 27) * ((~(\old(state) / (1ULL << 59)) + 1) % 32));
  */
uint32_t pcg32(void)
{
    uint64_t old = state;
    uint32_t shifted;
    uint32_t rot;

    state = old * N + inc;
    shifted = (uint32_t)(((old >> 18) ^ old) >> 27);
    rot = old >> 59;
    return (shifted >> rot) | (shifted << ((~rot + 1) & 31));
}

/**
 * Set the seed of the PCG32 sequence
 */
void pcg32_seed(uint64_t seed_state, uint64_t seed_sequence)
{
    state = 0;
    inc = (seed_sequence << 1) | 1;
    pcg32();
    state = state + seed_state;
    pcg32();
}
