# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver header for current Syscfg IPs
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd
syscfg_h = custom_target('gen_syscfg',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('syscfg'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'SYSCFG', '@INPUT@' ],
)
bsp_source_set.add(syscfg_h.to_list())

stm32_syscfg_dts_template_c = files(['stm32-syscfg-dt.c.in'])
stm32_syscfg_dts_template_h = files(['stm32-syscfg-dt.h.in'])

stm32_syscfg_dtsgen_c = dtsgen.process(stm32_syscfg_dts_template_c)
stm32_syscfg_dtsgen_h = dtsgen.process(stm32_syscfg_dts_template_h)

bsp_private_gen_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ stm32_syscfg_dtsgen_c, stm32_syscfg_dtsgen_h ])

# driver source selection
bsp_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32F4', if_true: files('stm32f4-syscfg.c'))

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_RP2350', 0) == 1
subdir('rp2350')
endif
