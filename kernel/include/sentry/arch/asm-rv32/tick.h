// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __ASM_TICK_H
#define __ASM_TICK_H

#include <inttypes.h>

void systime_init(void);

uint64_t systime_get_cycle(void);


/**
 * return the low word of the cycle counter
 */
static inline uint32_t systime_get_cyclel(void)
{
  //TODO
  return 0;
}

__attribute__((always_inline))
static inline uint64_t systime_get_seconds(void)
{
  //TODO
  return 0;
}

__attribute__((always_inline))
static inline uint64_t systime_get_milliseconds(void)
{
  //TODO
  return 0;
}

__attribute__((always_inline))
static inline uint64_t systime_get_microseconds(void) {
  //TODO
  return 0;
}

__attribute__((always_inline))
static inline uint64_t systime_get_nanoseconds(void) {
  //TODO
  return 0;
}

#endif /* __ASM_TICK_H */