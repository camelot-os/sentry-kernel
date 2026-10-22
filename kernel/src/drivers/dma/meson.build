# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

gpdma_h = custom_target('gen_gpdma',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('gpdma'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'GPDMA',
       '@INPUT@'
    ],
)

bsp_private_gen_header_set.add(gpdma_h)

# driver source selection
if kconfig_data.get('CONFIG_SOC_FAMILY_STM32', 0) == 1
subdir('st')
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_RP2350', 0) == 1
subdir('rp2350')
endif
