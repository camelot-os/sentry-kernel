# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

stm32_gpdma_dts_template_c = files(['stm32-gpdma-dt.c.in'])
stm32_gpdma_dts_template_h = files(['stm32-gpdma-dt.h.in'])

stm32_gpdma_dtsgen_c = dtsgen.process(stm32_gpdma_dts_template_c)
stm32_gpdma_dtsgen_h = dtsgen.process(stm32_gpdma_dts_template_h)

bsp_private_gen_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32U5', if_true: [ stm32_gpdma_dtsgen_c, stm32_gpdma_dtsgen_h ])

bsp_private_gen_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32U5', if_true: files('stm32u5-gpdma.c'))
