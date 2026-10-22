# SPDX-FileCopyrightText: 2026 ANSSI
# SPDX-License-Identifier: Apache-2.0

rp2350_rcc_dts_template_c = files(['rp2350-rcc-dt.c.in'])
rp2350_rcc_dts_template_h = files(['rp2350-rcc-dt.h.in'])

rp2350_rcc_dtsgen_c = dtsgen.process(rp2350_rcc_dts_template_c)
rp2350_rcc_dtsgen_h = dtsgen.process(rp2350_rcc_dts_template_h)

bsp_private_gen_source_set.add(rp2350_rcc_dtsgen_c)
bsp_private_gen_header_set.add(rp2350_rcc_dtsgen_h)

bsp_source_set.add(files(
    'rp2350-rcc.c',
    'rp2350-pwr.c',
))
