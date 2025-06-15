# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

jinja_gen = generator(jinja_cli,
       output: '@BASENAME@',
       arguments: ['-d', svd_json.full_path(),
                   '-o', '@OUTPUT@',
                   '@EXTRA_ARGS@',
                   '@INPUT@'],
       depends: [ svd_json ])

bsp_source_set = ssmod.source_set()
bsp_private_gen_source_set = ssmod.source_set()
bsp_private_gen_header_set = ssmod.source_set()
bsp_private_header_set = ssmod.source_set()

subdir('clk')
subdir('exti')
subdir('flash')
subdir('gpio')

# TODO w/ kconfig driver selector
# no rng IP for stm32f401
if kconfig_data.get('CONFIG_HAS_RNG', 0) == 1
subdir('rng')
endif

# subdir('syscfg')

if kconfig_data.get('CONFIG_DEBUG_OUTPUT_USART', 0) == 1
subdir('usart')
endif

if kconfig_data.get('CONFIG_HAS_GPDMA', 0) == 1
subdir('dma')
endif


bsp_source_set_config = bsp_source_set.apply(kconfig_data, strict: false)
bsp_private_gen_source_set_config = bsp_private_gen_source_set.apply(kconfig_data, strict: false)
bsp_private_gen_header_set_config = bsp_private_gen_header_set.apply(kconfig_data, strict: false)
bsp_private_header_set_config = bsp_private_header_set.apply(kconfig_data, strict: false)

sentry_bsp_lib = static_library(
    'sentry_bsp',
    sources: [
        bsp_source_set_config.sources(),
        bsp_private_gen_source_set_config.sources(),
        bsp_private_gen_header_set_config.sources(),
        bsp_header_set_config.sources(),
        bsp_private_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    install: false,
    c_args: [ target_arch_args, global_build_args, activated_lib_hardening_cflags ],
    dependencies: [ sentry_arch_dep, bsp_source_set_config.dependencies(), external_deps],
)

sentry_bsp_dep = declare_dependency(
    link_with: sentry_bsp_lib,
    sources: bsp_header_set_config.sources(),
    include_directories: kernel_inc,
)

sentry_bsp_lib_builddir = meson.current_build_dir() / 'libsentry_bsp.a.p'
#sentry_bsp_sources = custom_target(
#    'bsp_sources',
#    input: [
#        bsp_source_set_config.sources(),
#        bsp_private_gen_source_set_config.sources(),
#    ],
#    command: [ 'echo', '@INPUT@' ],
#    output: '@INPUT@'
#)
