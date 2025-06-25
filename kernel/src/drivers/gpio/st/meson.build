# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver header for current GPIO IPs
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd

stm32_drivers_gpio_files = files([
    'stm32-gpio.c',
    'stm32-pinctrl.c',
])

# XXX: generator ?
gpio_h = custom_target('gen_gpio',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('gpio'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'GPIO', '@INPUT@' ],
)

stm32_gpio_dts_template_c = files(['stm32-gpio-dt.c.in'])
stm32_gpio_dts_template_h = files(['stm32-gpio-dt.h.in'])

stm32_gpio_dtsgen_c = dtsgen.process(stm32_gpio_dts_template_c)
stm32_gpio_dtsgen_h = dtsgen.process(stm32_gpio_dts_template_h)

# driver source selection
bsp_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: stm32_drivers_gpio_files)
# XXX xxxx_h may be use in private gen header but not now ;-)
bsp_private_gen_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ stm32_gpio_dtsgen_c, stm32_gpio_dtsgen_h ])
bsp_private_gen_header_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ gpio_h ])
