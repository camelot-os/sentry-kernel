# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

arch_source_set = ssmod.source_set()

if kconfig_data.get('CONFIG_ARCH_ARM_CORTEX_M', 0) == 1
subdir('asm-cortex-m')
elif kconfig_data.get('CONFIG_ARCH_RV32', 0) == 1
subdir('asm-rv32')
endif

# architecture-generic, but architecture related code
arch_source_set.add(files(
  'asm-generic/platform.c',
  'asm-generic/sync.c',
  'asm-generic/panic.c',
))

arch_source_set_config = arch_source_set.apply(kconfig_data, strict:false)

sentry_arch_lib = static_library(
    'sentry_arch',
    sources: [
        arch_source_set_config.sources(),
        arch_header_set_config.sources(),
        managers_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    dependencies: [ arch_source_set_config.dependencies(), external_deps],
)

sentry_arch_dep = declare_dependency(
    link_with: sentry_arch_lib,
    sources: arch_header_set_config.sources(),
    include_directories: kernel_inc,
)
