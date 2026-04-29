// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#ifndef TEST_ZLIB_SHA256_NIST_PARSER_H
#define TEST_ZLIB_SHA256_NIST_PARSER_H

#include <stddef.h>
#include <stdint.h>

typedef int (*sha256_nist_vector_cb)(unsigned int len_bits,
                                     const uint8_t *msg,
                                     size_t msg_len,
                                     const uint8_t md[32],
                                     void *ctx);

int sha256_nist_parse_file(const char *path,
                           sha256_nist_vector_cb cb,
                           void *ctx,
                           size_t *executed_vectors);

#endif
