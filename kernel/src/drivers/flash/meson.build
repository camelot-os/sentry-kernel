# SPDX-FileCopyrightText: 2025 ANSSI
# SPDX-License-Identifier: Apache-2.0

if kconfig_data.get('CONFIG_SOC_FAMILY_STM32', 0) == 1
subdir('st')
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_OPENTITAN', 0) == 1
subdir('lowrisc')
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_RP2350', 0) == 1
subdir('rp2350')
endif
