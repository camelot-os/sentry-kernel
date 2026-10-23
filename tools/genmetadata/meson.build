# SPDX-FileCopyrightText: 2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

add_languages('cpp', native: true, required: true)

nl_json = dependency('nlohmann_json', native: true, version: '>=3.11')
argparse = dependency('argparse', native: true, version: '>=3')
openssl = dependency('openssl', native: true)

subdir('src')

genmetadata = executable(
    'genmetadata',
    genmetadata_src,
    cpp_args: [ '-include', fs.parent(kconfig_h) / fs.name(kconfig_h), ],
    include_directories: kernel_inc,
    link_language: 'cpp',
    override_options: ['cpp_std=gnu++20'],
    dependencies: [ nl_json, argparse, openssl ],
    build_by_default: true,
    install_dir: get_option('libexecdir'),
    native: true,
)

meson.add_install_script(
    sentry_install_script,
    genmetadata,
    get_option('bindir'),
    install_tag: 'bin-devel',
)
