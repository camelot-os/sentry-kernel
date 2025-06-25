// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef RV32_SEMIHOSTING_H
#define RV32_SEMIHOSTING_H

#ifdef __cplusplus
extern "C" {
#endif

/*REF: https://groups.google.com/a/groups.riscv.org/g/sw-dev/c/n-5VQ9PHZ4w/m/KbzH5t9MBgAJ */
static inline int __attribute__((always_inline)) semihosting_call(int reason, void *argPack)
{
  register int value asm("a0") = reason;
  register void *ptr asm("a1") = argPack;
  asm volatile(
      // Force 16-byte alignment to make sure that the 3 instructions fall
      // within the same virtual page.
      " .balign 16    \n"
      " .option push \n"
      // Force non-compressed RISC-V instructions
      " .option norvc \n"
      // semihosting e-break sequence
      " slli x0, x0, 0x1f \n" // # Entry NOP
      " ebreak \n"            // # Break to debugger
      " srai x0, x0,  0x7 \n" // # NOP encoding the semihosting call number 7
      " .option pop \n"
      /*mark (value) as an output operand*/
      : "=r"(value) /* Outputs */
      // The semihosting call number is passed in a0, and the argument in a1.
      : "0"(value), "r"(ptr) /* Inputs */
      // The "memory" clobber makes GCC assume that any memory may be arbitrarily read or written by the asm block,
      //  so will prevent the compiler from reordering loads or stores across it, or from caching memory values in registers across it.
      //  The "memory" clobber also prevents the compiler from removing the asm block as dead code.
      : "memory" /* Clobbers */
  );
  return value;
}

#ifdef __cplusplus
}
#endif

#endif /* ARM_SEMIHOSTING_H */