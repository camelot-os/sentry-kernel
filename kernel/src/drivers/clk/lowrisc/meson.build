# SPDX-FileCopyrightText: 2025 ANSSI
# SPDX-License-Identifier: Apache-2.0

bsp_clk_source_set = ssmod.source_set()

bsp_clk_source_set.add(files(
    'opentitan-pwr.c',
    'opentitan-rcc.c'
))

bsp_source_set.add_all(bsp_clk_source_set)