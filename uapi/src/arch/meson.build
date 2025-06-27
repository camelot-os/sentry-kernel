# SPDX-FileCopyrightText: 2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

uapi_modules += files('mod.rs')

if kconfig_data.get('CONFIG_ARCH_ARM_CORTEX_M', 0) == 1
uapi_modules += files('arm_cortex_m.rs')
endif

if kconfig_data.get('CONFIG_ARCH_RV32', 0) == 1
uapi_modules += files('riscv32.rs')
endif