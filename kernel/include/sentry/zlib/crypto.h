// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_CRYPTO_H
#define ZLIB_CRYPTO_H

#ifdef __cplusplus
extern "C" {
#endif

#include <inttypes.h>

/** \addtogroup CRC
 *  @{
 */

/*
    requires \valid(buf + (0 .. (len-1)));
    assigns buf[0 .. (len -1)];
   */
uint32_t crc32(unsigned char const * const buf, uint32_t len, uint32_t init);

/** @}*/

/** \addtogroup PGC32
 *  @{
 */
void pcg32_seed(uint64_t seed_state, uint64_t seed_sequence);
uint32_t pcg32(void);

/** @}*/

#ifdef __cplusplus
}
#endif

#endif/*!ZLIB_CRYPTO_H*/
