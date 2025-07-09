# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if kconfig_data.get('CONFIG_ARCH_ARM_CORTEX_M', 0) == 1
subdir('asm-cortex-m')
endif

if kconfig_data.get('CONFIG_ARCH_RV32', 0) == 1
subdir('riscv32')
endif