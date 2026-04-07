// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_CRYPTO_H
#define ZLIB_CRYPTO_H

#include <inttypes.h>

/** \addtogroup CRC
 *  @{
 */

/*@
   requires len >= 0;
   requires (len > 0 && buf != \null) ==> \valid_read(buf + (0 .. len - 1));
   assigns \nothing;
   // note: equivalence implies that crc32 never colisions
   ensures (len == 0 || buf == \null) ==> \result == \old(init);
*/
uint32_t crc32(unsigned char const * const buf, uint32_t len, uint32_t init);

/** @}*/

/** \addtogroup PGC32
 *  @{
 */

/*@ ghost int ghost_pcg32; */

/*@
  // assigns \nothing is false, as private variables are assigned.
  // To demonstrate to other components that there is no public side-effects,
  // we emulate a single ghost variable assignment here. Other assignments
  // are declared privately, with the function implementation (see zlib pcg32.c)
  assigns ghost_pcg32;
*/
void pcg32_seed(uint64_t seed_state, uint64_t seed_sequence);


/*@
  // same problem with same solution here
  assigns ghost_pcg32;
*/
uint32_t pcg32(void);

/** @}*/

#if CONFIG_SECU_METADATA_SHA256_CHECK
#define SHA256_STATE_SIZE 8
#define SHA256_BLOCK_SIZE 64
#define SHA256_DIGEST_SIZE 32

typedef struct {
  uint64_t sha256_total;
  uint32_t sha256_state[SHA256_STATE_SIZE];
  uint8_t sha256_buffer[SHA256_BLOCK_SIZE];
  uint64_t magic;
} sha256_context;

int sha256_init(sha256_context *ctx);
int sha256_update(sha256_context *ctx, const uint8_t *input, uint32_t ilen);
int sha256_final(sha256_context *ctx, uint8_t output[SHA256_DIGEST_SIZE]);
int sha256_scattered(const uint8_t **inputs, const uint32_t *ilens,
          uint8_t output[SHA256_DIGEST_SIZE]);
int sha256(const uint8_t *input, uint32_t ilen,
       uint8_t output[SHA256_DIGEST_SIZE]);
#endif


#endif/*!ZLIB_CRYPTO_H*/
