// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __ASM_UTILS_H
#define __ASM_UTILS_H

#define READ_CSR(reg)                               \
  ({                                                \
    unsigned long __tmp;                            \
    asm volatile ("csrr %0, " #reg : "=r"(__tmp));  \
    __tmp;                                          \
  })                                                \

#define WRITE_CSR(reg, value)                         \
  do {                                                \
    uint32_t __tmp = (value);                         \
    asm volatile ("csrw " #reg ", %0" ::"r"(__tmp));  \
  } while (0)                                         \

#endif /* __ASM_UTILS_H */
