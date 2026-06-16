// SPDX-FileCopyrightText: 2026 ANSSI
// SPDX-License-Identifier: Apache-2.0

#include <bsp/drivers/clk/rcc.h>

#if defined(CONFIG_SOC_SUBFAMILY_RP2350)
#include <sentry/arch/asm-cortex-m/buses.h>
#endif
#include <sentry/io.h>
#include <sentry/ktypes.h>
#include <sentry/managers/memory.h>

#include "rp2350-rcc-dt.h"

#ifndef BUSES_H
typedef enum bus_identifier {
    BUS_GENERIC = 0,
} bus_id_t;

#define BUS_IS_VALID(bus) (true)
#endif

#define RP2350_RESETS_RESET_REG         0x000u
#define RP2350_RESETS_RESET_DONE_REG    0x008u

#define RP2350_CLOCKS_REG_MAX_OFFSET    0x3ffu
#define RP2350_RESET_LINE_MAX_ID        28u
#define RP2350_RESET_TIMEOUT_ITERS      100000u

typedef enum rp2350_rcc_map_region {
    RP2350_RCC_MAP_REGION_CLOCKS = 0,
    RP2350_RCC_MAP_REGION_RESETS,
} rp2350_rcc_map_region_t;

static kstatus_t rp2350_rcc_map(rp2350_rcc_map_region_t region)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const rp2350_rcc_desc_t *desc = rp2350_rcc_get_desc();

    if (unlikely(desc == NULL)) {
        goto end;
    }

    switch (region) {
        case RP2350_RCC_MAP_REGION_CLOCKS:
            status = mgr_mm_map_kdev(desc->clocks_base_addr, desc->clocks_size);
            break;
        case RP2350_RCC_MAP_REGION_RESETS:
            status = mgr_mm_map_kdev(desc->resets_base_addr, desc->resets_size);
            break;
        default:
            status = K_ERROR_INVPARAM;
            break;
    }

end:
    return status;
}

static kstatus_t rp2350_rcc_unmap(void)
{
    return mgr_mm_unmap_kdev();
}

static inline bool rp2350_reset_mask_is_valid(uint32_t clk_msk)
{
    return ((clk_msk != 0u) && (clk_msk <= RP2350_RESET_LINE_MAX_ID));
}

static inline uint32_t rp2350_reset_line_to_mask(uint32_t reset_line)
{
    return (1u << reset_line);
}

static kstatus_t rp2350_set_reset_state(uint32_t reset_line, bool assert_reset)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const rp2350_rcc_desc_t *desc = rp2350_rcc_get_desc();
    uint32_t reg;
    uint32_t timeout;
    uint32_t reset_mask;
    bool mapped = false;

    if (unlikely((desc == NULL) || (desc->resets_base_addr == 0u) || (desc->resets_size == 0u) ||
                 !rp2350_reset_mask_is_valid(reset_line))) {
        goto end;
    }

    if (unlikely((status = rp2350_rcc_map(RP2350_RCC_MAP_REGION_RESETS)) != K_STATUS_OKAY)) {
        goto end;
    }
    mapped = true;

    reset_mask = rp2350_reset_line_to_mask(reset_line);

    reg = ioread32(desc->resets_base_addr + RP2350_RESETS_RESET_REG);
    if (assert_reset) {
        reg |= reset_mask;
    }
    else {
        reg &= ~reset_mask;
    }
    iowrite32(desc->resets_base_addr + RP2350_RESETS_RESET_REG, reg);

    timeout = RP2350_RESET_TIMEOUT_ITERS;
    while (timeout > 0u) {
        const uint32_t reset_done = ioread32(desc->resets_base_addr + RP2350_RESETS_RESET_DONE_REG);
        if (assert_reset) {
            if ((reset_done & reset_mask) == 0u) {
                status = K_STATUS_OKAY;
                goto end;
            }
        }
        else {
            if ((reset_done & reset_mask) != 0u) {
                status = K_STATUS_OKAY;
                goto end;
            }
        }
        timeout--;
    }

    status = K_ERROR_BUSY;

end:
    if (mapped) {
        rp2350_rcc_unmap();
    }
    return status;
}

kstatus_t rcc_probe(void)
{
    kstatus_t status;
    const rp2350_rcc_desc_t *desc = rp2350_rcc_get_desc();

    if (unlikely((desc == NULL) || (desc->clocks_base_addr == 0u) || (desc->clocks_size == 0u) ||
                 (desc->resets_base_addr == 0u) || (desc->resets_size == 0u))) {
        return K_ERROR_INVPARAM;
    }

    status = rp2350_rcc_map(RP2350_RCC_MAP_REGION_CLOCKS);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }
    rp2350_rcc_unmap();

    status = rp2350_rcc_map(RP2350_RCC_MAP_REGION_RESETS);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }
    rp2350_rcc_unmap();

    return K_STATUS_OKAY;
}

#if CONFIG_BUILD_TARGET_DEBUG
kstatus_t rcc_enable_debug_clockout(void)
{
    return K_STATUS_OKAY;
}
#endif

uint32_t rcc_get_core_frequency(void)
{
    return RP2350_DT_CORE_CLK_HZ;
}

kstatus_t rcc_enable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags)
{
    (void)flags;
    if (unlikely(!BUS_IS_VALID(busid))) {
        return K_ERROR_INVPARAM;
    }

    return rp2350_set_reset_state(clk_msk, false);
}

kstatus_t rcc_disable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags)
{
    (void)flags;
    if (unlikely(!BUS_IS_VALID(busid))) {
        return K_ERROR_INVPARAM;
    }

    return rp2350_set_reset_state(clk_msk, true);
}

kstatus_t rcc_get_bus_clock(bus_id_t busid, uint32_t *busclk)
{
    if (unlikely((busclk == NULL) || !BUS_IS_VALID(busid))) {
        return K_ERROR_INVPARAM;
    }
    *busclk = RP2350_DT_CORE_CLK_HZ;
    return K_STATUS_OKAY;
}

kstatus_t rcc_mux_select_clock_source(uint32_t clk_reg, uint32_t clkmsk, uint32_t val)
{
    kstatus_t status;
    const rp2350_rcc_desc_t *desc = rp2350_rcc_get_desc();
    uint32_t regval;
    uint32_t shift;
    bool mapped = false;

    if (unlikely((desc == NULL) || (desc->clocks_base_addr == 0u) || (desc->clocks_size == 0u) ||
                 (clk_reg > RP2350_CLOCKS_REG_MAX_OFFSET) || (clkmsk == 0u))) {
        return K_ERROR_INVPARAM;
    }

    shift = __builtin_ffs((int)clkmsk);
    if (unlikely(shift == 0u)) {
        return K_ERROR_INVPARAM;
    }

    status = rp2350_rcc_map(RP2350_RCC_MAP_REGION_CLOCKS);
    if (unlikely(status != K_STATUS_OKAY)) {
        return status;
    }
    mapped = true;

    regval = ioread32(desc->clocks_base_addr + clk_reg);
    regval &= ~clkmsk;
    regval |= ((val << (shift - 1u)) & clkmsk);
    iowrite32(desc->clocks_base_addr + clk_reg, regval);

    if (mapped) {
        rp2350_rcc_unmap();
    }

    return K_STATUS_OKAY;
}
