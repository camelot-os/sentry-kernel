// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef LOG_LEXER_H
#define LOG_LEXER_H

#include <stdarg.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdbool.h>

uint8_t print_with_len(const char *fmt, va_list *args, size_t *sizew);

uint16_t log_get_dbgbuf_offset(void);
uint8_t* log_get_dbgbuf(void);
void dbgbuffer_flush(void);

#endif/*!LOG_LEXER_H*/
