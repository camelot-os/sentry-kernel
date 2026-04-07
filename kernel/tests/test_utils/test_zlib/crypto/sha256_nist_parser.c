// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include "sha256_nist_parser.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int hex_nibble(char c)
{
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    c = (char)tolower((unsigned char)c);
    if (c >= 'a' && c <= 'f') {
        return c - 'a' + 10;
    }
    return -1;
}

static int decode_hex_alloc(const char *hex, uint8_t **out, size_t *out_len)
{
    size_t hex_len;
    uint8_t *buf = NULL;
    size_t i;

    if (hex == NULL || out == NULL || out_len == NULL) {
        return -1;
    }

    hex_len = strlen(hex);
    if ((hex_len % 2U) != 0U) {
        return -1;
    }

    *out_len = hex_len / 2U;
    if (*out_len == 0U) {
        *out = NULL;
        return 0;
    }

    buf = (uint8_t *)malloc(*out_len);
    if (buf == NULL) {
        return -1;
    }

    for (i = 0U; i < *out_len; i++) {
        int hi = hex_nibble(hex[2U * i]);
        int lo = hex_nibble(hex[2U * i + 1U]);
        if (hi < 0 || lo < 0) {
            free(buf);
            return -1;
        }
        buf[i] = (uint8_t)((hi << 4) | lo);
    }

    *out = buf;
    return 0;
}

int sha256_nist_parse_file(const char *path,
                           sha256_nist_vector_cb cb,
                           void *ctx,
                           size_t *executed_vectors)
{
    FILE *fp = NULL;
    char *line = NULL;
    size_t line_cap = 0U;
    ssize_t line_len;
    unsigned int len_bits = 0U;
    int has_len = 0;
    int has_msg = 0;
    uint8_t *msg = NULL;
    size_t msg_len = 0U;
    size_t count = 0U;

    if (path == NULL || cb == NULL || executed_vectors == NULL) {
        return -1;
    }

    fp = fopen(path, "r");
    if (fp == NULL) {
        return -1;
    }

    while ((line_len = getline(&line, &line_cap, fp)) >= 0) {
        char *p = line;
        uint8_t md[32];
        uint8_t *tmp = NULL;
        size_t tmp_len = 0U;

        while (*p == ' ' || *p == '\t') {
            p++;
        }
        if (*p == '#' || *p == '\n' || *p == '\0' || *p == '[') {
            continue;
        }

        if (strncmp(p, "Len = ", 6U) == 0) {
            unsigned long v = strtoul(p + 6U, NULL, 10);
            len_bits = (unsigned int)v;
            has_len = 1;
            continue;
        }

        if (strncmp(p, "Msg = ", 6U) == 0) {
            char *hex = p + 6U;
            char *eol = strpbrk(hex, "\r\n");
            if (eol != NULL) {
                *eol = '\0';
            }
            free(msg);
            msg = NULL;
            msg_len = 0U;
            if (decode_hex_alloc(hex, &msg, &msg_len) != 0) {
                free(line);
                fclose(fp);
                return -1;
            }
            has_msg = 1;
            continue;
        }

        if (strncmp(p, "MD = ", 5U) == 0) {
            char *hex = p + 5U;
            char *eol = strpbrk(hex, "\r\n");
            int cb_ret;
            const uint8_t *effective_msg = msg;
            size_t effective_msg_len = msg_len;
            if (eol != NULL) {
                *eol = '\0';
            }

            if (!has_len || !has_msg) {
                free(msg);
                free(line);
                fclose(fp);
                return -1;
            }
            if (len_bits == 0U) {
                effective_msg = NULL;
                effective_msg_len = 0U;
            } else {
                if ((len_bits % 8U) != 0U || (len_bits / 8U) != msg_len) {
                    free(msg);
                    free(line);
                    fclose(fp);
                    return -1;
                }
            }
            if (decode_hex_alloc(hex, &tmp, &tmp_len) != 0 || tmp_len != sizeof(md)) {
                free(tmp);
                free(msg);
                free(line);
                fclose(fp);
                return -1;
            }
            memcpy(md, tmp, sizeof(md));
            free(tmp);

            cb_ret = cb(len_bits, effective_msg, effective_msg_len, md, ctx);
            if (cb_ret != 0) {
                free(msg);
                free(line);
                fclose(fp);
                return -1;
            }

            count++;
            continue;
        }
    }

    free(msg);
    free(line);
    fclose(fp);
    *executed_vectors = count;
    return 0;
}
