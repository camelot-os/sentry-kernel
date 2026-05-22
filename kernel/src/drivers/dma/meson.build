# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

# for U5A5 GPDMA implementation, the register definitions are generated from the SVD file using jinja templates.
# This allows us to have a single source of truth for the register definitions and avoid manual errors.
if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32U5', 0) == 1

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

endif



stm32_gpdma_dts_template_c = files(['stm32-gpdma-dt.c.in'])
stm32_gpdma_dts_template_h = files(['stm32-gpdma-dt.h.in'])

stm32_gpdma_dtsgen_c = dtsgen.process(stm32_gpdma_dts_template_c)
stm32_gpdma_dtsgen_h = dtsgen.process(stm32_gpdma_dts_template_h)

# st-dma-v1 DTS-based controller definitions generation
stm32_dma_v1_dts_template_c = files(['stm32-st-dmav1-dt.c.in'])
stm32_dma_v1_dts_template_h = files(['stm32-st-dmav1-dt.h.in'])

stm32_dma_v1_dtsgen_c = dtsgen.process(stm32_dma_v1_dts_template_c)
stm32_dma_v1_dtsgen_h = dtsgen.process(stm32_dma_v1_dts_template_h)

# st-dma-v2 DTS-based controller definitions generation
stm32_dma_v2_dts_template_c = files(['stm32-st-dmav2-dt.c.in'])
stm32_dma_v2_dts_template_h = files(['stm32-st-dmav2-dt.h.in'])

stm32_dma_v2_dtsgen_c = dtsgen.process(stm32_dma_v2_dts_template_c)
stm32_dma_v2_dtsgen_h = dtsgen.process(stm32_dma_v2_dts_template_h)


# it seems that only the STM32u5 has the enhanced GPDMA
bsp_private_gen_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32U5', if_true: [ stm32_gpdma_dtsgen_c, stm32_gpdma_dtsgen_h ])
bsp_private_gen_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32U5', if_true: files('stm32u5-gpdma.c'))

# Other STM32 families have older GPDMA implementations, being st-dma-v1 or st-dma-v2 depending on the family
# the selection is made at soc subfamily level but the config name is unified for a more generic inclusion here
bsp_private_gen_source_set.add(when: 'CONFIG_HAS_GPDMA_ST_DMAV1', if_true: [ stm32_dma_v1_dtsgen_c, stm32_dma_v1_dtsgen_h ])
bsp_private_gen_source_set.add(when: 'CONFIG_HAS_GPDMA_ST_DMAV1', if_true: files('stm32-dmav1.c'))

bsp_private_gen_source_set.add(when: 'CONFIG_HAS_GPDMA_ST_DMAV2', if_true: [ stm32_dma_v2_dtsgen_c, stm32_dma_v2_dtsgen_h ])
bsp_private_gen_source_set.add(when: 'CONFIG_HAS_GPDMA_ST_DMAV2', if_true: files('stm32-dmav2.c'))

# driver source selection
