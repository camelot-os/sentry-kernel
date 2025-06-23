# SPDX-FileCopyrightText: 2025 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

if kconfig_data.get('CONFIG_SECU_ENABLE_EACSL', 0) == 1
eacsl_lib = static_library('eacsl',
    sources: [
        'eacsl.c',
    ],
    include_directories: [ kernel_inc ],
    c_args: [ target_arch_args, global_build_args ],
    dependencies: [
        external_deps
    ]   ,
    install: false,
)

sentry_eacsl_dep = declare_dependency(
    link_with: eacsl_lib,
    include_directories: kernel_inc,
)
else
# No EACSL support, just declare an empty dependency
sentry_eacsl_dep = declare_dependency(
    include_directories: kernel_inc,
)
endif
