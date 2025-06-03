// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __RISCV_UTILS_H
#define __RISCV_UTILS_H

#define CSR_READ(reg)                               \
  ({                                                \
    unsigned long __tmp;                            \
    asm volatile ("csrr %0, " #reg : "=r"(__tmp));  \
    __tmp;                                          \
  })                                                \

#define CSR_WRITE(reg, value)                         \
  do {                                                \
    uint32_t __tmp = (value);                         \
    asm volatile ("csrw " #reg ", %0" ::"r"(__tmp));  \
  } while (0)                                         \

#define CSR_SET(reg, bit) ({                                         \
  uint32_t tmp_reg;                                                  \
  asm volatile("csrrs %0, " #reg ", %1" : "=r"(tmp_reg) : "rK" bit); \
  })

#define CSR_CLEAR(reg, bit) ({                                       \
  uint32_t tmp_reg;                                                  \
  asm volatile("csrrc %0, " #reg ", %1" : "=r"(tmp_reg) : "rK" bit); \
  })

/**
 * M-mode interrupts bit in MIE
 */
#define MIE_SI (1 << 3)  // Software interrupt
#define MIE_TI (1 << 7)  // Timer interrupt
#define MIE_EI (1 << 11) // External interrupt

#endif /* __RISCV_UTILS_H */
