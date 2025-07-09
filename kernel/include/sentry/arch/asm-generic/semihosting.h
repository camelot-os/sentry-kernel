// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef ARCH_GEN_SEMIHOSTING_H
#define ARCH_GEN_SEMIHOSTING_H

/**
 * \file semihosting entrypoint
 */

#ifdef __cplusplus
extern "C" {
#endif

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/semihosting.h>
#elif defined(__x86_64__)
// TODO add semihosting
#elif defined(__i386__)
// TODO add semihosting
#elif defined(CONFIG_ARCH_RV32)
#include <sentry/arch/asm-rv32/semihosting.h>
#else
#error "unsupported architecture!"
#endif

#define SYS_OPEN        0x01
#define SYS_CLOSE       0x02
#define SYS_WRITEC      0x03
#define SYS_WRITE0      0x04
#define SYS_WRITE       0x05
#define SYS_READ        0x06
#define SYS_READC       0x07
#define SYS_ISERROR     0x08
#define SYS_ISTTY       0x09
#define SYS_SEEK        0x0A
#define SYS_FLEN        0x0C
#define SYS_TMPNAME     0x0D
#define SYS_REMOVE      0x0E
#define SYS_RENAME      0x0F
#define SYS_CLOCK       0x10
#define SYS_TIME        0x11
#define SYS_SYSTEM      0x12
#define SYS_ERRNO       0x13
#define SYS_GET_CMDLINE 0x15
#define SYS_HEAPINFO    0x16
#define SYS_EXIT        0x18
#define SYS_ELAPSED     0x30
#define SYS_TICKFREQ    0x31

#define SYS_FILE_MODE_READ              0
#define SYS_FILE_MODE_READBINARY        1
#define SYS_FILE_MODE_READWRITE         2
#define SYS_FILE_MODE_READWRITEBINARY   3
#define SYS_FILE_MODE_WRITE             4
#define SYS_FILE_MODE_WRITEBINARY       5
#define SYS_FILE_MODE_WRITEREAD         6
#define SYS_FILE_MODE_WRITEREADBINARY   7
#define SYS_FILE_MODE_APPEND            8
#define SYS_FILE_MODE_APPENDBINARY      9
#define SYS_FILE_MODE_APPENDREAD        10
#define SYS_FILE_MODE_APPENDREADBINARY  11

/**
 * @brief open a file on host operating system
 *
 * @param filename pointer to null-terminated string containing file or device name
 * @param mode file opening mode
 * @param length filename string length (w/o null character)
 *
 * @return -1 on error, file handle on success
 */
static inline int semihosting_open(const char* filename, int mode, int length)
{
    int argv[3];

    argv[0] = (int)filename;
    argv[1] = mode;
    argv[2] = length;

    return semihosting_call(SYS_OPEN, argv);
}

static inline int semihosting_close(int file)
{
    int argv[1];

    argv[0] = file;

    return semihosting_call(SYS_CLOSE, argv);
}

static inline int semihosting_writec(char c)
{
    return semihosting_call(SYS_WRITEC, (int *)&c);
}

static inline int semihosting_write0(const char* s)
{
    return semihosting_call(SYS_WRITE0, (int *)s);
}

static inline int semihosting_write(int file, const char* buffer, int length)
{
    int argv[3];

    argv[0] = file;
    argv[1] = (int)buffer;
    argv[2] = length;

    return semihosting_call(SYS_WRITE, argv);
}

#ifdef __cplusplus
}
#endif

#endif/*!#ifndef ARCH_GEN_SEMIHOSTING_H*/
