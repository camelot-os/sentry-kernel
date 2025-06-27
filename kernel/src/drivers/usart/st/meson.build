# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# very same header name, generated from corresponding svd
usart_h = custom_target('gen_usart',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('usart'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'USART',
       '@INPUT@'
    ],
)

lpuart_h = custom_target('gen_lpuart',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('lpuart'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'LPUART',
       '@INPUT@'
    ],
)

stm32_usart_dts_template_c = files(['stm32-usart-dt.c.in'])
stm32_usart_dts_template_h = files(['stm32-usart-dt.h.in'])

stm32_usart_dtsgen_c = dtsgen.process(stm32_usart_dts_template_c)
stm32_usart_dtsgen_h = dtsgen.process(stm32_usart_dts_template_h)

bsp_source_set.add(files('usart.c'))

bsp_private_gen_header_set.add(when: 'CONFIG_DRV_STM32_USART', if_true: usart_h)
bsp_private_gen_header_set.add(when: 'CONFIG_DRV_STM32_LPUART', if_true: lpuart_h)

# driver source selection
bsp_source_set.add(when: 'CONFIG_DRV_STM32_USART', if_true: files('stm32-usart.c'))
bsp_source_set.add(when: 'CONFIG_DRV_STM32_LPUART', if_true: files('stm32-lpuart.c'))

bsp_private_gen_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ stm32_usart_dtsgen_c, stm32_usart_dtsgen_h ])
