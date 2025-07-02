// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>
#include <uapi/uapi.h>

/**
 * log_lexer delivered printf POSIX compliant implementation
 */
uint8_t print_with_len(const char *fmt, va_list *args, size_t *sizew);

uint16_t log_get_dbgbuf_offset(void);
uint8_t* log_get_dbgbuf(void);
void dbgbuffer_flush(void);


static inline void dbgbuffer_display(void)
{
    uint16_t len = log_get_dbgbuf_offset();
    copy_to_kernel(log_get_dbgbuf(), len);
    __sys_log(len);
}


size_t strnlen(const char *s, size_t maxlen)
{
    size_t result = 0;

    if (s == NULL) {
        /** TODO: panic to be called */
        goto err;
    }

    while ((s[result] != '\0') && result < maxlen) {
        result++;
    }
err:
    return result;
}

/*************************************************************
 * libstream exported API implementation: POSIX compilant API
 ************************************************************/

/*
 * Linux-like printk() API (no kernel tagging by now)
 */
__attribute__ ((format (printf, 1, 2))) int printf(const char *fmt, ...)
{
    va_list args;
    size_t  len;
    int res = -1;

    dbgbuffer_flush();
    if (fmt == NULL) {
        goto err;
    }
    /*
     * if there is some asyncrhonous printf to pass to the kernel, do it
     * before execute the current printf command
     */
    va_start(args, fmt);
    if (print_with_len(fmt, &args, &len) == 0) {
        res = (int)len;
    }
    va_end(args);
    if (res == -1) {
        dbgbuffer_flush();
        goto err;
    }
    /* display to debug output */
    dbgbuffer_display();
err:
    dbgbuffer_flush();
    return res;
}
