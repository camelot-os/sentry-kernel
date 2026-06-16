# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver header for current GPIO IPs
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd
exti_h = custom_target('gen_gpio',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('exti'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'EXTI', '@INPUT@' ],
)


stm32_exti_dts_template_h = files(['stm32-exti-dt.h.in'])
stm32_exti_dts_template_c = files(['stm32-exti-dt.c.in'])
stm32_exti_dtsgen_h = dtsgen.process(stm32_exti_dts_template_h)
stm32_exti_dtsgen_c = dtsgen.process(stm32_exti_dts_template_c)

# driver source selection

bsp_private_gen_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ stm32_exti_dtsgen_h, stm32_exti_dtsgen_c ])
bsp_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-exti.c'))
bsp_private_gen_header_set.add([ exti_h ])

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_RP2350', 0) == 1
subdir('rp2350')
endif
