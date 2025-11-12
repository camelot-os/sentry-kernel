// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __DWT_H
#define __DWT_H

#include <inttypes.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/io.h>

/*@
  assigns CoreDebug->DEMCR, DWT->CTRL;
 */
__STATIC_FORCEINLINE void dwt_enable_cyccnt(void)
{
    CoreDebug->DEMCR |= CoreDebug_DEMCR_TRCENA_Msk;
    DWT->CTRL |= DWT_CTRL_CYCCNTENA_Msk;
}

__STATIC_FORCEINLINE void platform_enable_cyccnt(void)__attribute__((alias("dwt_enable_cyccnt")));

/*@
  assigns DWT->CTRL;
 */
__STATIC_FORCEINLINE void dwt_disable_cyccnt(void)
{
    DWT->CTRL &= ~DWT_CTRL_CYCCNTENA_Msk;
}

__STATIC_FORCEINLINE void platform_disable_cyccnt(void)__attribute__((alias("dwt_disable_cyccnt")));

/*@
  assigns DWT->CYCCNT;
 */
__STATIC_FORCEINLINE void dwt_reset_cyccnt(void)
{
    DWT->CYCCNT = 0;
}

__STATIC_FORCEINLINE void platform_reset_cyccnt(void)__attribute__((alias("dwt_reset_cyccnt")));

/*@
  assigns \nothing;
 */
__STATIC_FORCEINLINE uint32_t dwt_cyccnt(void)
{
    return DWT->CYCCNT;
}

__STATIC_FORCEINLINE uint32_t platform_get_cyccnt(void)__attribute__((alias("dwt_cyccnt")));

#endif /* __ARCH_PERFO_H */
