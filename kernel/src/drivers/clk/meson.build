# SPDX-FileCopyrightText: 2025 ANSSI
# SPDX-License-Identifier: Apache-2.0

if kconfig_data.get('CONFIG_ARCH_ARM_CORTEX_M', 0) == 1
subdir('st')
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_OPENTITAN', 0) == 1
subdir('lowrisc')
endif