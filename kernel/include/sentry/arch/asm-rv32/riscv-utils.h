// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __RISCV_UTILS_H
#define __RISCV_UTILS_H

#ifdef __cplusplus
extern "C" {
#endif

#define CSR_READ(reg)                             \
  ({                                              \
    unsigned long res;                            \
    asm volatile ("csrr %0, " #reg : "=r"(res));  \
    res;                                          \
  })

#define CSR_WRITE(reg, value) ({                     \
    uint32_t __tmp = (value);                        \
    asm volatile ("csrw " #reg ", %0" ::"r"(__tmp)); \
  })

#define CSR_ZERO_ADDR(reg_addr)                    \
    asm volatile ("csrw %0, zero" ::"I"(reg_addr));

#define CSR_WRITE_ADDR(reg, value) ({                         \
  if (__builtin_constant_p(value) && (unsigned long)(value) < 32) \
    __asm__ volatile ("csrw " #reg ", %0" :: "i"(value)); \
  else \
    __asm__ volatile ("csrw " #reg ", %0" :: "r"(value)); })

#define CSR_READ_ADDR(reg_addr)                                \
  ({                                                           \
    unsigned long res;                                         \
    asm volatile ("csrr %0, %1"  : "=r"(res) : "I"(reg_addr)); \
    res;                                                       \
  })

#define CSR_SET(reg, bit) ({                                           \
  uint32_t tmp_reg;                                                    \
  asm volatile("csrrs %0, " #reg ", %1" : "=r"(tmp_reg) : "rK" (bit)); \
  })

#define CSR_CLEAR(reg, bit) ({                                         \
  uint32_t tmp_reg;                                                    \
  asm volatile("csrrc %0, " #reg ", %1" : "=r"(tmp_reg) : "rK" (bit)); \
  })

/**
 * M-mode interrupts bit in MIE
 */
#define MIE_SI (1 << 3)  // Software interrupt
#define MIE_TI (1 << 7)  // Timer interrupt
#define MIE_EI (1 << 11) // External interrupt

#ifdef __cplusplus
}
#endif

#endif /* __RISCV_UTILS_H */
