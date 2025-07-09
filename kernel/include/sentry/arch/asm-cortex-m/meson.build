# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# list of statically defined headers
arch_header_set.add(files(
    'io.h',
    'membarriers.h',
    'mpu.h',
    'mpu_pmsa_v7.h',
    'nvic.h',
    'platform.h',
    'scb.h',
    'soc.h',
    'system.h',
    'systick.h',
    'thread.h',
    'semihosting.h',
))

arch_header_set.add(when: 'CONFIG_HAS_MPU_PMSA_V7', if_true: files('mpu_pmsa_v7.h'))
arch_header_set.add(when: 'CONFIG_HAS_MPU_PMSA_V8', if_true: files('mpu_pmsa_v8.h'))

irq_defs_in = files('irq_defs.h.in')
# generated headers
irq_def_h = custom_target('gen_irq_defs',
   input: irq_defs_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

layout_h = custom_target('gen_layout',
    input: layout_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

core_in = files('core.h.in')

core_h = custom_target('gen_core',
    input: core_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

arch_header_set.add(
    irq_def_h.to_list(),
    layout_h.to_list(),
    core_h.to_list(),
)

# the way we generate the buses list depend on the SoC family. To do
# that, the input jinja template is selected depending on the configured SOC
# family or subfamily
buses_h_in_set = ssmod.source_set()
buses_h_in_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32F4', if_true: files('stm32f4-buses.h.in'))
buses_h_in_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32L4', if_true: files('stm32l4-buses.h.in'))
# FIXME: use the same as L4 for U5 family
# rework this as this is weak
buses_h_in_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32U5', if_true: files('stm32l4-buses.h.in'))
buses_h_in_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32WB', if_true: files('stm32l4-buses.h.in'))

# here, we can add other templates for other ARM SoC famillies if needed
buses_h_in_set_config = buses_h_in_set.apply(kconfig_data, strict: false)

if buses_h_in_set_config.sources().length() != 0
    buses_h = custom_target('gen_buses',
        input: buses_h_in_set_config.sources(),
        output: 'buses.h',
        depends: [ svd_json ],
        command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'RCC', '@INPUT@' ],
    )

    arch_header_set.add(buses_h.to_list())
else
    warning('Missing bus definition for SoC @0@'.format(kconfig_data.get('CONFIG_ARCH_SOCNAME')))
endif
