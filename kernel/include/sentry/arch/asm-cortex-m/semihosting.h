// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARM_SEMIHOSTING_H
#define ARM_SEMIHOSTING_H

/**
 * @brief Make a Thumb mode semihosting system call
 *
 * @param op semihosting call operation code
 * @param argv argument array
 *
 * Semihosting call is automagically catch by debugger if enable in its side.
 * In thumb mode, every time the CPU break on "0xAB" breakpoint (thumb opcode `0xbeab`)
 * debugger will fetch `r0` (op) and `r1` (argv) registers and execute the corresponding system call
 * in the host environment.
 *
 * The second automagically trick here is that arm eabi defined that the first arg is in `r0`
 * and the second in `r1`. So, there is **nothing** to do but preventing the compiler to trim
 * these away. So, this function is **never** inlined and non optimized.
 *
 * Debugger will then write `r0` with syscall return code, so, there is **nothing** (again) to do
 * but return (i.e. branching to link register).
 *
 * For all these reason, there is no need for prolog nor epilog, thus this is a naked function.
 *
 * @warning do not use this without enabling semihosting on debugger side, otherwise
 *          core will hang until reset.
 *
 * @return host executed call return code
 */

__attribute__((noinline, naked, optimize("-O0")))
static int semihosting_call(int op __UNUSED, int* argv __UNUSED)
{
#ifndef __FRAMAC__
    asm inline (
        "bkpt #0xAB     \n\t\
         bx lr          \n\t\
        ");
#else
    return 0;
#endif/*!__FRAMAC__*/
}

#endif /* ARM_SEMIHOSTING_H */
