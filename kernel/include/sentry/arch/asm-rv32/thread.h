// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __THREAD_H
#define __THREAD_H

/**
 * \file context manipulation, including kernel threads
 */
#include <inttypes.h>
#include <stddef.h>

#ifndef __FRAMAC__

/* RISC-V typical stack frame */
typedef struct stack_frame {
    /**< backed by default handler */
    uint32_t ra;   // return address
    uint32_t gp;   // Global pointer
    uint32_t tp;   // Thread pointer
    uint32_t t0, t1, t2, t3, t4, t5, t6; // Temporary registers
    uint32_t s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11;
    uint32_t a0, a1, a2, a3, a4, a5, a6, a7;
} __attribute__((packed)) stack_frame_t;

static inline stack_frame_t *__thread_init_stack_context(uint32_t rerun, size_t sp, size_t pc, size_t got, uint32_t seed)
{
    stack_frame_t*  frame = (stack_frame_t*)(sp - sizeof(stack_frame_t));
    frame->ra = pc;

    frame->gp = got;
    frame->tp = got;

    frame->t0 = 0;
    frame->t1 = 0;
    frame->t2 = 0;
    frame->t3 = 0;
    frame->t4 = 0;
    frame->t5 = 0;
    frame->t6 = 0;

    frame->s0 = 0;
    frame->s1 = 0;
    frame->s2 = 0;
    frame->s3 = 0;
    frame->s4 = 0;
    frame->s5 = 0;
    frame->s6 = 0;
    frame->s7 = 0;
    frame->s8 = 0;
    frame->s9 = 0;
    frame->s10 = 0;
    frame->s11 = 0;

    frame->a0 = 0;
    frame->a1 = 0;
    frame->a2 = 0;
    frame->a3 = 0;
    frame->a4 = 0;
    frame->a5 = 0;
    frame->a6 = 0;
    frame->a7 = 0;

    return frame;
}
#endif

#endif/*__THREAD_H*/
