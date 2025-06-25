# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# source set that hold all libarch relative public headers
arch_header_set = ssmod.source_set()

if kconfig_data.get('CONFIG_ARCH_ARM_CORTEX_M', 0) == 1
subdir('asm-cortex-m')
elif kconfig_data.get('CONFIG_ARCH_RV32', 0) == 1
subdir('asm-rv32')
endif

subdir('asm-generic')

arch_header_set_config = arch_header_set.apply(kconfig_data, strict:false)
