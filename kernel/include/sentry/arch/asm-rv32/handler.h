// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLER_H
#define HANDLER_H

#include <sentry/arch/asm-rv32/thread.h>

/*@
  assigns \nothing
 */
static inline __attribute__((noreturn)) void __do_panic(void) {
  // TODO: call security manager cleanup
  do {
#ifndef __FRAMAC__
    asm volatile ("nop");
#endif
  } while (1);
}

#ifdef __FRAMAC__
stack_frame_t *svc_handler(stack_frame_t *frame);
#endif

#endif /* HANDLER_H */