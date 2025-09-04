// SPDX-FileCopyrightText: 2025 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

#ifndef SECURITY_MANAGER_H
#define SECURITY_MANAGER_H

#include <uapi/uapi.h>
#include <sentry/ktypes.h>

#include <sentry/managers/capability.h>

#ifdef __cplusplus
extern "C" {
#endif

/** @def mask for dev capability. dev capa hold 11 first bytes of register */
#define CAP_DEV_MASK ((0x1UL  << 12) - 1)
/** @def mask for sys capability, hold bits 12-15 */
#define CAP_SYS_MASK (((0x1UL  << 16) - 1) & ~CAP_DEV_MASK)
/** @def mask for mem capability */
#define CAP_MEM_MASK (((0x1UL << 20) - 1) & ~(CAP_DEV_MASK | CAP_SYS_MASK))

kstatus_t mgr_security_init(void);

kstatus_t mgr_security_entropy_generate(uint32_t *seed);

kstatus_t mgr_security_get_capa(taskh_t tsk, uint32_t *capas);

secure_bool_t mgr_security_has_dev_capa(taskh_t tsk);

secure_bool_t mgr_security_has_sys_capa(taskh_t tsk);

secure_bool_t mgr_security_has_capa(taskh_t tsk, capability_t  capa);

secure_bool_t mgr_security_has_oneof_capas(taskh_t tsk, uint32_t capas);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_security_autotest(void);

kstatus_t mgr_security_set_capa(capability_t);

kstatus_t mgr_security_clear_capa(capability_t);
#endif

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
