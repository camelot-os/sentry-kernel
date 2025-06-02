// SPDX-FileCopyrightText: ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include <sentry/arch/asm-rv32/systick.h>

static uint64_t cycle_jiffies;
static uint64_t dwt_snap;

void systime_init(void)
{

  systick_init();
}

uint64_t systime_get_cycle(void)
{
  return cycle_jiffies;
}