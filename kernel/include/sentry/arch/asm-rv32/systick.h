// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef SYSTICK_H_
#define SYSTICK_H_

#include <inttypes.h>
#include <sentry/thread.h>

/*
 * the use of ghost allows to validate temporal behavior and local globals states
 * without the need of real code inclusion. ghosts do not exist out of the Frama-C
 * context
 */
/*@ ghost bool ghost_systick_initialized = false; */

/* FIXME to set*/
#define CONFIG_SYSTICK_HZ 1000

#define JIFFIES_TO_SEC(x)  ((x) / CONFIG_SYSTICK_HZ)
#define JIFFIES_TO_MSEC(x) ((x) * 1000UL / CONFIG_SYSTICK_HZ)
#define SEC_TO_JIFFIES(x)  ((x) * CONFIG_SYSTICK_HZ)
#define MSEC_TO_JIFFIES(x) ((x) * CONFIG_SYSTICK_HZ / 1000UL)

typedef uint64_t jiffies_t;

/*@
  requires ghost_systick_initialized;
  assigns \nothing;
 */
jiffies_t systime_get_jiffies(void);

/*@
    assigns ghost_systick_initialized;
    assigns *((SysTick_Type*)SysTick_BASE);
 */
void systick_init(void);

/*@
    requires ghost_systick_initialized;
    assigns *((SysTick_Type*)SysTick_BASE);
 */
stack_frame_t *systick_handler(stack_frame_t * stack_frame);


/*@
    assigns *((SysTick_Type*)SysTick_BASE);
 */
void systick_stop_and_clear(void);

#endif /* SYSTICK_H_ */