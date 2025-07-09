// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/usart/usart.h>
#include <bsp/drivers/clk/rcc.h>
#include <sentry/zlib/compiler.h>
#if CONFIG_DEBUG_OUTPUT_SEMIHOSTING
#include <sentry/arch/asm-generic/semihosting.h>
#endif
#include "log.h"
#include "logo.h"
/**
 * @brief probe the debug backend
 *
 * by now, only kernel serial output is probbed. Other debug I/O can be
 * imagined/configured, such as leds, etc...
 */
kstatus_t mgr_debug_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_DEBUG_OUTPUT_USART
    status = usart_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
#endif
#ifdef CONFIG_BUILD_TARGET_DEBUG
    status = rcc_enable_debug_clockout();
#endif
    dbgbuffer_flush();
#if CONFIG_DEBUG_OUTPUT_USART
    logo_print();
end:
#endif
    return status;
}

/**
 * @brief raw log export, abstracting the selected output log device
 *
 * typically used for sys_log() syscall as no parsing is made in kernelspace
 *
 * @param[in] logbuf: input log buffer
 * @param[in] len: log buffer len
 */
kstatus_t debug_rawlog(__MAYBE_UNUSED const uint8_t *logbuf, __MAYBE_UNUSED size_t len)
{
#if CONFIG_DEBUG_OUTPUT_USART
    /* usart as no notion of the byte type it emit. sending unsigned content */
    return usart_tx(logbuf, len);
#elif CONFIG_DEBUG_OUTPUT_SEMIHOSTING
    kstatus_t status = K_ERROR_NOENT;
    /*
     * XXX:
     * Filename must be aligned on word boundary as it is use as semi-hosted syscall arguments,
     * Which is an array of int, and thus must be aligned.
     */
#ifndef __FRAMAC__
    /** NOTE: Frama-C do not yet support C11 _Alignas */
    _Alignas(size_t)
#endif
    static const char filename[] = CONFIG_DEBUG_SEMIHOSTING_OUTPUT_FILE;
    int fd;

    fd = semihosting_open(filename, SYS_FILE_MODE_APPEND, sizeof(filename) - 1);
    if (fd < 0) {
        goto err;
    }
    semihosting_write(fd, logbuf, len);
    semihosting_close(fd);
err:
    return status;
#else
    /* in release or no output mode, if called, just do nothing */
    return K_STATUS_OKAY;
#endif
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_debug_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
