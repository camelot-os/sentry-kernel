# SPDX-FileCopyrightText: 2024 - 2025 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# NOTE: the timer identifier may vary from SoC familly to another, and as such
# the string may be a per CONFIG_SOC value
timer_h = custom_target('gen_timer',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('timer'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'TIM',
       '@INPUT@'
    ],
)

stm32_timer_dts_template_c = files('stm32-basic-timer-dt.c.in')
stm32_timer_dts_template_h = files('stm32-basic-timer-dt.h.in')
stm32_timer_dts_dtsgen_c = dtsgen.process(stm32_timer_dts_template_c)
stm32_timer_dts_dtsgen_h = dtsgen.process(stm32_timer_dts_template_h)

stm32_timer_dts_dtsgen_dep = declare_dependency(
  sources: stm32_timer_dts_dtsgen_h,
)

autotest_driver_timer_src = [
    timer_h,
    stm32_timer_dts_dtsgen_c,
    stm32_timer_dts_dtsgen_h,
    files('stm32-basic-timer.c'),
]

autotest_sourceset.add(when: 'CONFIG_AUTOTEST_TIMER_DRIVER', if_true: autotest_driver_timer_src)
