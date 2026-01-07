// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/dwt.h>
#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/arch/asm-cortex-m/debug.h>
#include <sentry/arch/asm-cortex-m/handler.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/memory.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>
#include <sentry/syscalls.h>
#include <sentry/io.h>

#include <uapi/types.h>

#define HANDLER_SVC_ENTRY
#include <sentry/arch/asm-generic/handler-svc-lut.h>
/**
 * @file ARM Cortex-M generic handlers
 */

/* .bss informations generated in ldscript */
extern uint32_t _sbss;
extern uint32_t _ebss;
extern uint32_t _sidata;
extern uint32_t _sdata;
extern uint32_t _edata;

extern __irq_handler_t __vtor_table[];

/**
 * NOTE: the frame dump just do nothing (pr_ are empty macros) in release mode
 */
static inline void dump_frame(stack_frame_t *frame)
{
    uint32_t msp, psp;
    pr_emerg("== frame info");
    asm volatile (
        "mrs %0, msp\r\n"   /* r0 <- MSP */
        "mrs %1, psp\r\n"   /* or r0 <- PSP (process stack) */
    : "=r" (msp), "=r" (psp) ::);
    pr_emerg("msp\t\t\t%08x\t%08d", msp, msp);
    pr_emerg("psp\t\t\t%08x\t%08d", psp, psp);
    pr_emerg("[%08x] r4\t\t%08x\t%08d", &frame->r4, frame->r4, frame->r4);
    pr_emerg("[%08x] r5\t\t%08x\t%08d", &frame->r5, frame->r5, frame->r5);
    pr_emerg("[%08x] r6\t\t%08x\t%08d", &frame->r6, frame->r6, frame->r6);
    pr_emerg("[%08x] r7\t\t%08x\t%08d", &frame->r7, frame->r7, frame->r7);
    pr_emerg("[%08x] r8\t\t%08x\t%08d", &frame->r8, frame->r8, frame->r8);
    pr_emerg("[%08x] r9\t\t%08x\t%08d", &frame->r9, frame->r9, frame->r9);
    pr_emerg("[%08x] r10\t\t%08x\t%08d", &frame->r10, frame->r10, frame->r10);
    pr_emerg("[%08x] r11\t\t%08x\t%08d", &frame->r11, frame->r11, frame->r11);
    pr_emerg("[%08x] lr\t\t%08x\t%08d", &frame->lr, frame->lr, frame->lr);
    pr_emerg("[%08x] r0\t\t%08x\t%08d", &frame->r0, frame->r0, frame->r0);
    pr_emerg("[%08x] r1\t\t%08x\t%08d", &frame->r1, frame->r1, frame->r1);
    pr_emerg("[%08x] r2\t\t%08x\t%08d", &frame->r2, frame->r2, frame->r2);
    pr_emerg("[%08x] r3\t\t%08x\t%08d", &frame->r3, frame->r3, frame->r3);
    pr_emerg("[%08x] r12\t\t%08x\t%08d", &frame->r12, frame->r12, frame->r12);
    pr_emerg("[%08x] prev_lr\t%08x\t%08d", &frame->prev_lr, frame->prev_lr, frame->prev_lr);
    pr_emerg("[%08x] pc\t\t%08x\t%08d", &frame->pc, frame->pc, frame->pc);
    pr_emerg("[%08x] xpsr\t\t%08x\t%08d", &frame->xpsr, frame->xpsr, frame->xpsr);
}

__STATIC_FORCEINLINE secure_bool_t is_userspace_fault(stack_frame_t *frame) {
    secure_bool_t res = SECURE_FALSE;
    if (likely(frame->lr & 0x4UL)) {
        res = SECURE_TRUE;
    }
    return res;
}

__STATIC_FORCEINLINE stack_frame_t *may_panic(stack_frame_t *frame) {
    stack_frame_t *newframe = frame;
    if (is_userspace_fault(frame) == SECURE_TRUE) {
        taskh_t tsk = sched_get_current();
        /* user mode, fault source is userspace:
         *  1. set task as faulted
         *  2. elect another task
         */
        pr_debug("[%lx] Userspace Oops!", tsk);
        mgr_task_set_state(tsk, JOB_STATE_FAULT);
#ifdef CONFIG_SECU_RESET_ON_USERFAULT
        /* force reset on userspace fault, be cautious as it can lead to DoS */
        system_reset();
#else
        tsk = sched_elect();
        mgr_task_get_sp(tsk, &newframe);
#endif
    } else {
        __do_panic();
        __builtin_unreachable();
    }
    return newframe;
}

/*
 * Replaced by real sentry _entrypoint at link time
 */
extern  __attribute__((noreturn)) void _entrypoint();

__STATIC_FORCEINLINE __attribute__((noreturn)) void hardfault_handler(stack_frame_t *frame)
{
    pr_emerg("Hardfault!!!");
    if ((SCB->HFSR) & SCB_HFSR_FORCED_Pos) {
        pr_emerg("hardfault forced (escalation)");
    } else {
        pr_emerg("direct hardfault, no escalation");
    }
    if ((SCB->HFSR) & SCB_HFSR_VECTTBL_Pos) {
        pr_emerg("Bus fault during vector table read.");
    }
#if defined(CONFIG_BUILD_TARGET_DEBUG)
    #if 0
    /* XXX: To be implemented, helper associated to kernel map */
    mgr_debug_dump_stack(frame);
    #endif
#endif
    dump_frame(frame);
    __platform_clear_flags();
    request_data_membarrier();
    __do_panic();
}

__STATIC_FORCEINLINE stack_frame_t *usagefault_handler(stack_frame_t *frame)
{
    stack_frame_t *newframe = frame;
    size_t cfsr = SCB->CFSR;
    pr_emerg("Usagefault!!!");
    if (cfsr & SCB_CFSR_UNDEFINSTR_Msk) {
        pr_emerg("Undefined instruction!");
    }
    if (cfsr & SCB_CFSR_INVSTATE_Msk) {
        pr_emerg("invalid state!");
    }
    if (cfsr & SCB_CFSR_INVPC_Msk) {
        pr_emerg("invalid PC!");
    }
    if (cfsr & SCB_CFSR_NOCP_Msk) {
        pr_emerg("No coprocessor!");
    }
    if (cfsr & SCB_CFSR_UNALIGNED_Msk) {
        pr_emerg("Unaligned memory access!");
    }
    if (cfsr & SCB_CFSR_DIVBYZERO_Msk) {
        pr_emerg("Division by 0!");
    }
    dump_frame(frame);
    newframe = may_panic(frame);
    __platform_clear_flags();
    request_data_membarrier();
    return newframe;
}


__STATIC_FORCEINLINE stack_frame_t *memfault_handler(stack_frame_t *frame)
{
    stack_frame_t *newframe = frame;
    size_t cfsr = SCB->CFSR;
    pr_err("Memory fault !!!");
    if (cfsr & SCB_CFSR_IACCVIOL_Msk) {
        pr_emerg("Instruction access violation!");
    }
    if (cfsr & SCB_CFSR_DACCVIOL_Msk) {
        pr_emerg("Data access violation!");
    }
    if (cfsr & SCB_CFSR_MUNSTKERR_Msk) {
        pr_emerg("Fault while unstacking from exception!");
    }
    if (cfsr & SCB_CFSR_MSTKERR_Msk) {
        pr_emerg("Fault while stacking for exception entry!");
    }
    if (cfsr & SCB_CFSR_MMARVALID_Msk) {
        pr_emerg("Fault at address %p", SCB->MMFAR);
    }
    dump_frame(frame);
    newframe = may_panic(frame);
    request_data_membarrier();
    return newframe;
}


#define __GET_SVCNUM(pc, syscallnum) ({ \
    asm volatile ("ldrh  r1, [%0,#-2]\n\t"    \
                  "bic   %1, r1, #0xFF00\r\t" \
                  : "=r" (syscallnum)         \
                  : "r" (pc)                  \
                  : "r1", "memory"            \
                  );})

#ifdef __FRAMAC__
/**
 * NOTE: In Frama-C mode, we make input syscall num value randomized over 0-255,
 * so that all supported syscalls are executed, and invalid syscall num is
 * also considered
 */
extern volatile uint8_t Frama_C_entropy_source_u8 __attribute__((unused));
#endif

#ifndef __FRAMAC__
__STATIC_FORCEINLINE
#endif
stack_frame_t *svc_handler(stack_frame_t *frame)
{
    /* C implementation first */
    uint8_t syscall_id = 0;
    stack_frame_t *next_frame = frame;
    const lut_svc_handler *svc_lut;

#ifndef __FRAMAC__
    __GET_SVCNUM(frame->pc, syscall_id);
#else
    syscall_id = Frama_C_entropy_source_u8;
#endif
    if (unlikely(syscall_id >= svc_lut_size())) {
        lut_unsuported(frame);
        goto err;
    }
    svc_lut = svc_lut_get();
    next_frame = (svc_lut[syscall_id])(frame);
err:
    return next_frame;
}

#define __GET_IPSR(intr) ({ \
    asm volatile ("mrs r1, ipsr\n\t" \
                  "mov %0, r1\n\t" \
                  : "=r" (intr) :: "r1" ); })

/**
 * demap current task downto svc_exchange only. has sence only when userspace is running
 */
static inline void demap_task_protected_area(void) {
    if (unlikely(mgr_task_is_userspace_spawned() == SECURE_FALSE)) {
        goto end;
    }
    taskh_t current = sched_get_current();
    /* resize current task mapping to SVC Exchange only now that its stack is saved
       from now on, the kernel do not have anymore access to the task data, except the
       svc_exchange area
     */
    if (unlikely(mgr_mm_resize_taskdata_to_svcexchange(current) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
end:
    return;
}

/**
 * @brief dispatcher and generic handler manager
 *
 * may not return the same frame pointer as received (through r0),
 * depending on the IRQ.
 *
 */
stack_frame_t *Default_SubHandler(stack_frame_t *frame)
{
    int it;
    stack_frame_t *newframe = frame;
    taskh_t current = sched_get_current();
    taskh_t next;
    Status statuscode;


    /* get back interrupt name */
    __GET_IPSR(it);
    it &= IPSR_ISR_Msk;

    /*
     * As the vector received is unified for both core exception (negatives)
     * and NVIC interrupts (starting with 0), we need to decrement the vtor
     * value of 16 to realign.
     * This is required as the IRQ canonical name used by the NVIC start
     * at 0 for the first peripheral interrupt, which is, in term of
     * VTOR, the 16th one.
     */
    it-= 16;

    /* sync task ctx SP with current frame, always required */
    mgr_task_set_sp(current, (stack_frame_t*)__get_PSP());

    /* distatching here */
    switch (it) {
        case HARDFAULT_IRQ:
            /* calling hardfault handler */
            hardfault_handler(frame);
            /*@ assert \false; */
        case MEMMANAGE_IRQ:
            newframe = memfault_handler(frame);
            break;
        case USAGEFAULT_IRQ:
            newframe = usagefault_handler(frame);
            break;
        case SVC_IRQ:
            demap_task_protected_area();
            newframe = svc_handler(frame);
            break;
        case SYSTICK_IRQ:
            demap_task_protected_area();
            /* periodic, every each millisecond execution */
            newframe = systick_handler(frame);
            break;
        default:
            demap_task_protected_area();
            if (it >= 0) {
                newframe = userisr_handler(frame, it);
            }
            /* defaulting to nothing... */
            /* We might assert on spurious/unahndled exception here ? */
            break;
    }

    /* the next job may not be the previous one */
    next = sched_get_current();
    if (likely(mgr_task_is_userspace_spawned())) {
        mgr_mm_map_task(next);
    }
    /*
     * get back target syscall return code, if in comming back to a previously preempted syscall
     */

    if (likely(mgr_task_get_sysreturn(next, &statuscode) == K_STATUS_OKAY)) {
        /* a syscall return code as been previously set in this context and not cleared
         * by the handler. This means that the next job has been preempted during a syscall,
         * whatever the reason is. We then get back the current syscall value now and update it
         *
         * It is to note here that a statuscode of type STATUS_NON_SENSE must not happend as it
         * means that a syscall that do not know synchronously its own return code has not seen
         * its return value being updated in the meantime **before** coming back to the job
         */
        if (unlikely(statuscode == STATUS_NON_SENSE)) {
            __do_panic();
        }
        newframe->r0 = statuscode;
        /* clearing the sysreturn. next job is no more syscall-preempted */
        mgr_task_clear_sysreturn(next);
    }
    return newframe;
}


/**
 * @brief Reset handler, executed at POR time
 */
__attribute__((noreturn, used)) void Reset_Handler(void)
{
    uint32_t *src;
    uint32_t *p;
    uint32_t shcsr;
    __disable_irq();

    /* enable dwt cycle counter at the very beginning */
    dwt_enable_cyccnt();
    dwt_reset_cyccnt();

    /*
     * TODO:
     * Add a 'LOAD_FROM_ANYWHERE or something' config flag
     * In such a case, we can't make any assumption regarding
     * the current cpu state, so disable and clear any pending irq,
     * relocate vtor and set msp to the given value.
     */
    for (uint32_t irqnum = 0; irqnum < __NVIC_VECTOR_LEN; irqnum++) {
        nvic_disableirq(irqnum);
        nvic_clear_pendingirq(irqnum);
    }

    systick_stop_and_clear();

    /* relocate vtor table */
    SCB->VTOR = (uint32_t)&__vtor_table[0];
    /* set main stack pointer to reset value */
    __set_MSP((uint32_t)__vtor_table[0]);

    /* enable FPU access if used */
#if defined (__FPU_USED) && (__FPU_USED == 1U)
    SCB->CPACR |= ((3U << 10U*2U) |     /* enable CP10 Full Access */
                   (3U << 11U*2U)  );   /* enable CP11 Full Access */
#endif

#ifndef __FRAMAC__
    /** NOTE: there is no notion of link time based memory information in Frama-C AST */
    /* clear bss */
    for (p = &_sbss; p < &_ebss; p++) {
        *p = 0UL;
    }

    /* data relocatation */
    /* XXX:
     *  /!\ We may relocate only data.rel.ro section /!\
     */
    for (src = &_sidata, p = &_sdata; p < &_edata; p++) {
        *p = *src++;
    }
#endif

    /* enable supported fault handlers */
    shcsr = SCB_SHCSR_USGFAULTENA_Msk |
            SCB_SHCSR_MEMFAULTENA_Msk;
    iowrite32((size_t)&SCB->SHCSR, shcsr);
    /* branch to sentry kernel entry point */
    _entrypoint();

    /* should never return in nominal mode */
    /* in Frama-C, this function do return */
    /*@ assert \true; */
}

/**
 * XXX:
 *  We do not support privileged, FPU context saving, nor secure thread by now.
 *  But we should save `control` on task frame at exception entry and restore
 *  privilege and FPU context at exception return.
 */

__STATIC_FORCEINLINE void save_context(void)
{
    asm volatile (
    "cpsid   i\r\n"         /* Disable all interrupts */
    "dsb \r\n"
    "isb \r\n"
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack */
    "ite     eq\r\n"        /* if equal 0 */
    "mrseq   r0, msp\r\n"   /* r0 <- MSP */
    "mrsne   r0, psp\r\n"   /* or r0 <- PSP (process stack) */
    "stmfd   r0!, {r4-r11, lr}\r\n"
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack */
    "ite     eq\r\n"        /* if equal 0 */
    "msreq   msp, r0\r\n"   /* MSP <- r0 */
    "msrne   psp, r0\r\n"   /* PSP <- r0 */
    "isb \r\n"
    ::: "memory" );
}

__STATIC_FORCEINLINE void restore_context(void)
{
    asm volatile (
    "ldmfd   r0!, {r4-r11, lr}\r\n"
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack      */
    "ite     eq\r\n"        /* if equal 0 */
    "msreq   msp, r0\r\n"   /* MSP <- r0 */
    "msrne   psp, r0\r\n"   /* PSP <- r0 */
    "isb\r\n"
    "cpsie   i\r\n"
    "dsb \r\n"
    "isb \r\n"
    "bx      lr\r\n"
    ::: "memory");
}

/**
 * @brief Default handler for all others
 *
 * TODO: fix some of the asm that can be done with inline function instead, to
 * avoid redundancy. By now, some others handlers are missing, (hardfault, svc....)
 * that will require some generic handler entry/leave asm code
 */
__attribute__((naked, used)) void Default_Handler(void)
{
    save_context();
    asm volatile (
        "bl Default_SubHandler" ::: "memory"
    );
    restore_context();
}
