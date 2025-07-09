// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef PLIC_H
#define PLIC_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <sentry/ktypes.h>

#include <sentry/arch/asm-rv32/riscv-utils.h>
#include <sentry/arch/asm-rv32/membarriers.h>

#define NUM_IRQS 2

kstatus_t interrupt_enable_irq(uint32_t IRQn);
kstatus_t interrupt_disable_irq(uint32_t IRQn);
uint32_t interrupt_get_pending_irq(uint32_t IRQn);
kstatus_t interrupt_set_pending_irq(uint32_t IRQn);
kstatus_t interrupt_clear_pendingirq(uint32_t IRQn);

/*@
  assigns \nothing;
 */
static inline void interrupt_disable(void)
{
#ifndef __FRAMAC__
  CSR_WRITE(mie, 0);
#endif
  return;
}

/*@
  assigns \nothing;
 */
static inline void interrupt_enable(void)
{
#ifndef __FRAMAC__
  CSR_SET(mie, MIE_EI | MIE_SI | MIE_TI);
  arch_data_sync_barrier();
  arch_inst_sync_barrier();
#endif
  return;
}

/*@
  requires __NVIC_VECTOR_LEN <= NVIC_MAX_ALLOWED_IRQS;
  assigns *NVIC;
 */
static inline void interrupt_init(void)
{
  // TODO
  return;
}

#ifdef __cplusplus
}
#endif

#endif /* PLIC_H */