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
   requires buf != \null ==> \valid_read(buf + (0 .. len - 1));
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


#endif/*!ZLIB_CRYPTO_H*/
