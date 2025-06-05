// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-rv32/semihosting.h>
#include <sentry/ktypes.h>

#define SH_SYS_OPEN 0x01
#define SH_SYS_CLOSE 0x02
#define SH_SYS_WRITE0 0x04
#define SH_SYS_WRITE 0x05



int semihosting_open(const char *filename, int length, int mode)
{
  uint32_t args[3] = {
    (uint32_t) filename,
    (uint32_t) (mode),
    (uint32_t) length
  };

  return sys_sh(SH_SYS_OPEN, (void *) args);
}

int semihosting_close(int file)
{
  uint32_t args[1] = {(uint32_t) file};

  return sys_sh(SH_SYS_CLOSE, (void *) args);
}

int semihosting_write(int file, const char *buffer, int length)
{
  uint32_t args[3] = {
    (uint32_t) file,
    (uint32_t) buffer,
    (uint32_t) length
  };

  return sys_sh(SH_SYS_WRITE, (void *) args);
}