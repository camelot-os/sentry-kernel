# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver headers for current Clock IP. This include PLL control and power headers
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd


# local components source_sets. These sources set hold
# - local sources
# - corresponding exported header
# - private sources that are generated
# - private headers that are generated
# - private headers (not generated)
bsp_clk_source_set = ssmod.source_set()
bsp_clk_header_set = ssmod.source_set()
bsp_clk_private_gen_source_set = ssmod.source_set()
bsp_clk_private_gen_header_set = ssmod.source_set()
bsp_clk_private_header_set = ssmod.source_set()

# first, generate all sources and headers, based on config,  and add
# them to the corresponding source set (see above)

# starting with
rcc_h = custom_target('gen_rcc',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('rcc'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'RCC', '@INPUT@' ],
)
bsp_clk_private_header_set.add(rcc_h.to_list())

if kconfig_data.get('CONFIG_SOC_FAMILY_STM32', 0) == 1

stm32_rcc_c_template = files('stm32-rcc.c.in')
stm32_rcc_h_template = files('stm32-rcc.h.in')

stm32_rcc_dt_c_template = files('stm32-rcc-dt.c.in')
stm32_rcc_dt_h_template = files('stm32-rcc-dt.h.in')

# private generated source set
stm32_rcc_c = custom_target('gen_stm32_rcc_c',
    input: stm32_rcc_c_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

stm32_rcc_dt_c = custom_target('gen_stm32_rcc_dt_c',
    input: stm32_rcc_dt_c_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

bsp_clk_private_gen_source_set.add(stm32_rcc_c, stm32_rcc_dt_c)

# private generated header set
stm32_rcc_h = custom_target('gen_stm32_rcc_h',
    input: stm32_rcc_h_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)


stm32_rcc_dt_h = custom_target('gen_stm32_rcc_dt_h',
    input: stm32_rcc_dt_h_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

bsp_clk_private_gen_header_set.add(stm32_rcc_h, stm32_rcc_dt_h)
endif # CONFIG_SOC_FAMILY_STM32

# XXX: there is no OR clause in source set

# private source set
bsp_clk_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32F4', if_true: files('stm32x4-pll.c'))
bsp_clk_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32L4', if_true: files('stm32x4-pll.c'))

bsp_clk_source_set.add(
    when: 'CONFIG_SOC_SUBFAMILY_STM32U5',
    if_true: files(
        'stm32u5-pll.c',

        'stm32u5-pwr.c',

        'stm32u5-rcc.c',
    ),
)

bsp_clk_private_header_set.add(
    when: 'CONFIG_SOC_SUBFAMILY_STM32U5',
    if_true: files(
    'stm32u5-pll.h',
    'stm32u5-pwr.h',
    ),
)

# per subfamily RCC additions
if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32F4', 0) == 1
stm32f4_rcc_c_template = files('stm32f4-rcc.c.in')
stm32f4_rcc_h_template = files('stm32f4-rcc.h.in')

stm32f4_rcc_c = dtsgen.process(
    stm32f4_rcc_c_template,
    preserve_path_from: meson.current_source_dir(),
)
stm32f4_rcc_h = dtsgen.process(
    stm32f4_rcc_h_template,
    preserve_path_from: meson.current_source_dir(),
)

bsp_clk_private_gen_source_set.add(stm32f4_rcc_c)
bsp_clk_private_gen_header_set.add(stm32f4_rcc_h)
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32L4', 0) == 1
stm32l4_rcc_c_template = files('stm32l4-rcc.c.in')
stm32l4_rcc_h_template = files('stm32l4-rcc.h.in')

stm32l4_rcc_c = dtsgen.process(
    stm32l4_rcc_c_template,
    preserve_path_from: meson.current_source_dir(),
)
stm32l4_rcc_h = dtsgen.process(
    stm32l4_rcc_h_template,
    preserve_path_from: meson.current_source_dir(),
)

bsp_clk_private_gen_source_set.add(stm32l4_rcc_c)
bsp_clk_private_gen_header_set.add(stm32l4_rcc_h)
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32U5', 0) == 1
stm32u5_rcc_h_template = files('stm32u5-rcc.h.in')
stm32u5_rcc_h = dtsgen.process(
    stm32u5_rcc_h_template,
    preserve_path_from: meson.current_source_dir(),
)
bsp_clk_private_gen_header_set.add(stm32u5_rcc_h)
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32WB', 0) == 1
stm32wb_rcc_c_template = files('stm32wb-rcc.c.in')
stm32wb_rcc_c = dtsgen.process(
    stm32wb_rcc_c_template,
    preserve_path_from: meson.current_source_dir(),
)
bsp_clk_private_gen_source_set.add(stm32wb_rcc_c)
stm32wb_rcc_h_template = files('stm32wb-rcc.h.in')
stm32wb_rcc_h = dtsgen.process(
    stm32wb_rcc_h_template,
    preserve_path_from: meson.current_source_dir(),
)
bsp_clk_private_gen_header_set.add(stm32wb_rcc_h)
endif

pwr_h = custom_target('gen_pwr',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('pwr'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'PWR', '@INPUT@' ],
)
bsp_clk_header_set.add(pwr_h.to_list())

# driver source selection
bsp_clk_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-pwr.c'))

# now that all clk module sources and headers are added/generated, we
# add them to the upper library sources (libbsp)
bsp_source_set.add_all(bsp_clk_source_set, bsp_clk_header_set)
bsp_private_gen_source_set.add_all(bsp_clk_private_gen_source_set)
bsp_private_gen_header_set.add_all(bsp_clk_private_gen_header_set)
bsp_private_header_set.add_all(bsp_clk_private_header_set)
