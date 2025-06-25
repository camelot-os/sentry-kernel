// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-rv32/plic.h>

/**
 * @brief Get Hart ID in m-mode
 */
static inline uint32_t get_hart_id()
{
    uint32_t id;
    asm volatile("csrr %0, mhartid"
                    : "=r" (id));
    return id;
}

kstatus_t interrupt_enable_irq(uint32_t IRQn)
{
    uint32_t hart_id = get_hart_id();

    // TODO : correct register access and bit setting

    // Set default priority for all IRQ
    *(uint32_t *)PLIC_PRIORITY(IRQn) = 1;
    // Enable IRQ for the hart
    *(uint32_t *)PLIC_MENABLE(hart_id) |= (1 << IRQn);
    // Set 0 priority threshold
    *(uint32_t *)PLIC_MTHRESHOLD(hart_id) = 0;
}

kstatus_t interrupt_disable_irq(uint32_t IRQn)
{
    // TODO
    return K_ERROR_UNKNOWN;
}

uint32_t  interrupt_get_pending_irq(uint32_t IRQn)
{
    // TODO
    return K_ERROR_UNKNOWN;
}

kstatus_t interrupt_set_pending_irq(uint32_t IRQn)
{
    // TODO
    return K_ERROR_UNKNOWN;
}

kstatus_t interrupt_clear_pendingirq(uint32_t IRQn)
{
    // TODO
    return K_ERROR_UNKNOWN;
}