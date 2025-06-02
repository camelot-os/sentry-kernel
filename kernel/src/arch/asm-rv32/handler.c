// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>

#include <sentry/sched.h>

#include <sentry/arch/asm-rv32/asm_utils.h>
#include <sentry/arch/asm-rv32/thread.h>
#include <sentry/arch/asm-rv32/systick.h>
#include <sentry/arch/asm-rv32/handler.h>

/* Asynchronous trap - interrupts */
#define MCAUSE_MSWINT  0x80000003 // Machine software interrupt
#define MCAUSE_MTIMER  0x80000007 // Machine Timer interrupt
#define MCAUSE_MEXTINT 0x8000000B // Machine external interrupt
#define MCAUSE_CNTOVF  0x8000000D // Counter overflow

/* Synchronous trap - exceptions */
#define MCAUSE_IADDRMIS 0x00000000 // Instruction address misaligned
#define MCAUSE_IACCFLT  0x00000001 // Instruction access fault
#define MCAUSE_ILLINSTR 0x00000002 // Illegal instruction
#define MCAUSE_BREAKPT  0x00000003 // Breakpoint
#define MCAUSE_DADDRMIS 0x00000004 // Load address misaligned
#define MCAUSE_DACCFLT  0x00000005 // Load access fault
#define MCAUSE_SADDRMIS 0x00000006 // Store/AMO address misaligned
#define MCAUSE_SACCFLT  0x00000007 // Store/AMO access fault
#define MCAUSE_UCALL    0x00000008 // Environment call from U-mode
#define MCAUSE_MCALL    0x0000000B // Environment call from M-mode
#define MCAUSE_IPGFAULT 0x0000000C // Instruction page fault
#define MCAUSE_LPGFAULT 0x0000000D // Load page fault
#define MCAUSE_SPGFAULT 0x0000000F // Store/AMO page fault
#define MCAUSE_SWCHECK  0x00000012 // Software check
#define MCAUSE_HWERROR  0x00000013 // Hardware error

/* .bss informations generated in ldscript */
extern uint32_t _sbss;
extern uint32_t _ebss;
extern uint32_t _sidata;
extern uint32_t _sdata;
extern uint32_t _edata;

static inline void demap_task_protected_area(void) {
  // TODO: remove unused PMP regions
  // TODO: move to dedicated file ?
}

#ifndef __FRAMAC__
static inline
#endif
stack_frame_t *svc_handler(stack_frame_t *frame)
{
  // TODO

  return frame;
}

static inline __attribute__((noreturn)) void hardfault_handler(stack_frame_t *frame)
{
  // TODO: dump frame for debug

  __do_panic();
}

/**
 * @brief Dispatcher and generic handler manager
 *
 * May not return the same frame pointer as received depending on the IRQ
 */
stack_frame_t *handle_trap(stack_frame_t *frame)
{
  uint32_t mcause  = READ_CSR(mcause);
  uint32_t mtval   = READ_CSR(mtval);
  uint32_t user_pc = READ_CSR(mepc);

  stack_frame_t *newframe = frame;

  taskh_t current = sched_get_current();
  taskh_t next;

  if (mcause & 0x80000000) {
    /* Interrupts */
    switch (mcause) {
      case MCAUSE_MSWINT:
        // TODO
        break;
      case MCAUSE_MTIMER:
        demap_task_protected_area();
        newframe = systick_handler(frame);
        break;
      case MCAUSE_MEXTINT:
        // TODO
        break;
      case MCAUSE_CNTOVF:
        // TODO
        hardfault_handler(frame);
        /*@ assert \false; */
        break;
    }
  } else {
    /* Exceptions */
    // TODO
  }

  return newframe;
}

/**
 * @brief Save context on the stack
 *
 * Use scratch register as temporary storage to save stack pointer
 * Do not save FPU registers
 * Set stack pointer in `a0`
 *
 * TODO: align frame on definition given in thread.h
 */
__attribute__((naked, used)) void save_context(void)
{
  asm volatile (
    "csrrw sp, mscratch, sp\n" // Store SP in mscratch
    "addi sp, sp, -4 * 31\n"   // Allocate stack storage space
    "sw ra,  4 * 0(sp)\n"      // Store context on stack
    "sw gp,  4 * 1(sp)\n"
    "sw tp,  4 * 2(sp)\n"
    "sw t0,  4 * 3(sp)\n"
    "sw t1,  4 * 4(sp)\n"
    "sw t2,  4 * 5(sp)\n"
    "sw t3,  4 * 6(sp)\n"
    "sw t4,  4 * 7(sp)\n"
    "sw t5,  4 * 8(sp)\n"
    "sw t6,  4 * 9(sp)\n"
    "sw a0,  4 * 10(sp)\n"
    "sw a1,  4 * 11(sp)\n"
    "sw a2,  4 * 12(sp)\n"
    "sw a3,  4 * 13(sp)\n"
    "sw a4,  4 * 14(sp)\n"
    "sw a5,  4 * 15(sp)\n"
    "sw a6,  4 * 16(sp)\n"
    "sw a7,  4 * 17(sp)\n"
    "sw s0,  4 * 18(sp)\n"
    "sw s1,  4 * 19(sp)\n"
    "sw s2,  4 * 20(sp)\n"
    "sw s3,  4 * 21(sp)\n"
    "sw s4,  4 * 22(sp)\n"
    "sw s5,  4 * 23(sp)\n"
    "sw s6,  4 * 24(sp)\n"
    "sw s7,  4 * 25(sp)\n"
    "sw s8,  4 * 26(sp)\n"
    "sw s9,  4 * 27(sp)\n"
    "sw s10, 4 * 28(sp)\n"
    "sw s11, 4 * 29(sp)\n"
    "csrr a0, mscratch\n"       // Set a0 to stack pointer
    "sw a0, 4 * 30(sp)\n"
  );
}

/**
 * @brief Restore context from the stack
 */
__attribute__((naked, used)) void restore_context(void)
{
  asm volatile (
    "lw ra,  4 * 0(sp)\n"
    "lw gp,  4 * 1(sp)\n"
    "lw tp,  4 * 2(sp)\n"
    "lw t0,  4 * 3(sp)\n"
    "lw t1,  4 * 4(sp)\n"
    "lw t2,  4 * 5(sp)\n"
    "lw t3,  4 * 6(sp)\n"
    "lw t4,  4 * 7(sp)\n"
    "lw t5,  4 * 8(sp)\n"
    "lw t6,  4 * 9(sp)\n"
    "lw a0,  4 * 10(sp)\n"
    "lw a1,  4 * 11(sp)\n"
    "lw a2,  4 * 12(sp)\n"
    "lw a3,  4 * 13(sp)\n"
    "lw a4,  4 * 14(sp)\n"
    "lw a5,  4 * 15(sp)\n"
    "lw a6,  4 * 16(sp)\n"
    "lw a7,  4 * 17(sp)\n"
    "lw s0,  4 * 18(sp)\n"
    "lw s1,  4 * 19(sp)\n"
    "lw s2,  4 * 20(sp)\n"
    "lw s3,  4 * 21(sp)\n"
    "lw s4,  4 * 22(sp)\n"
    "lw s5,  4 * 23(sp)\n"
    "lw s6,  4 * 24(sp)\n"
    "lw s7,  4 * 25(sp)\n"
    "lw s8,  4 * 26(sp)\n"
    "lw s9,  4 * 27(sp)\n"
    "lw s10, 4 * 28(sp)\n"
    "lw s11, 4 * 29(sp)\n"
    "lw sp,  4 * 30(sp)\n"
    "sret\n"
  );
}

/**
 * @brief Default handler for all traps
 *
 * Align function on 4-byte boundary because `stvec` also holds flags in
 *  its lower 2 bits
 */
__attribute__((naked, used))
__attribute__((aligned(4)))
void Default_Handler(void)
{
  save_context();
  asm volatile("call handle_trap");
  restore_context();
}

/*
 * Replaced by real sentry _entrypoint at link time
 */
extern  __attribute__((noreturn)) void _entrypoint();

/**
 * @brief Reset handler
 *
 * From privileged spec §3.4
 *
 * Start in M mode
 * MIE and MPRV are reset to 0
 * MISA reset to support all extensions
 * PC is set to implementation defined reset vector
 * MCAUSE contains cause of the reset
 * PMP registers are set to 0
 */
__attribute__((noreturn, used)) void Reset_Handler(void)
{
  uint32_t *src;
  uint32_t *p;

  // Disable interrupts
  WRITE_CSR(mie, 0);
  // Select normal memory access privilege level
  // WRITE_CSR(csrw, 0);

  // TODO: enable cycle counts ?

  // TODO: disable and clear pending IRQ

  // TODO: stop and clear systick

  // Register trap handler
  WRITE_CSR(mtvec, (uint32_t) Default_Handler);

  // TODO: set main stack pointer

#ifndef __FRAMAC__
  // Clear bss
  for (p = &_sbss; p < &_ebss; p++) {
    *p = 0UL;
  }

  // Data relocation
  for (src = &_sidata, p = &_sdata; p < &_edata; p++) {
    *p = *src++;
  }
#endif

  // TODO: enable supported fault handlers

  // Branch to sentry kernel entry point
  _entrypoint();

  /* should never return in nominal mode */
  /* in Frama-C, this function do return */
  /*@ assert \true; */
}