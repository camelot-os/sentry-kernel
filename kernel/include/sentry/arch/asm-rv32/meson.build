# SPDX-FileCopyrightText: ANSSI
# SPDX-License-Identifier: Apache-2.0

mtimer_template_h = files('mtimer.h.in')

mtimer_h = dtsgen.process(mtimer_template_h)

arch_header_set.add(
  mtimer_h
)

arch_header_set.add(files(
  'buses.h',
  'handler.h',
  'io.h',
  'membarriers.h',
  'platform.h',
  'plic.h',
  'pmp.h',
  'riscv-utils.h',
  'semihosting.h',
  'systick.h',
  'thread.h',
  'tick.h',
))