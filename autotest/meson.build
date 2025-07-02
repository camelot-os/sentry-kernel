# SPDX-FileCopyrightText: 2023 - 2025 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

if not with_autotest
    subdir_done()
endif

if meson.is_subproject()
warning('!!! Are you sure you want to build the autotest task as a subproject ?')
endif

autotest_task_name = 'autotest'
autotest_map_file = '@0@.map'.format(autotest_task_name)

# local tool for easy ELF parsing to json file
parseelf = find_program('parseelf.py', required: true, dirs: [meson.project_source_root() / 'tools'])

subdir('common')

autotest_ldscript = custom_target('autotest_ldscript',
    input: autotest_ldscript_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

autotest_linker_args = [
    '-T' + autotest_ldscript.full_path(),
    '-z', 'noexecstack',
]

if kconfig_data.get('CONFIG_AUTOTEST_C', 0) == 1
subdir('c')
elif kconfig_data.get('CONFIG_AUTOTEST_RUST', 0) == 1
subdir('rust')
else
error('unknown autotest backend')
endif

# Set rust toolchain config entry according to kconfig
# # Note:
# #   configuration_file is done at top level meson.build in order to generate
# #   rust-toolchain.toml at build root directory.
# rust_toolchain_in = files('src/tests/src-rs/rust-toolchain.toml.in')
# rust_toolchain_config = configuration_data()
# rust_toolchain_config.set('channel', get_option('rust-channel'))
# rust_toolchain_config.set('target', kconfig_data.get_unquoted('CONFIG_RUSTC_TARGET'))

# global_rust_build_args = [
#     '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs),
#     target_rustargs,
#     '-C', 'lto=true', '-C', 'relocation-model=pic', '-C', 'link-args=--emit-relocs'
# ]

autotest_hex = custom_target(
    input: autotest_elf,
    output: '@BASENAME@.hex',
    command: [
        objcopy,
        '-O', 'ihex',
        '@INPUT@',
        '@OUTPUT@'
    ],
    install: true,
    install_dir: get_option('bindir'),
    install_tag: 'runtime',
)

autotest_json = custom_target(
    input: autotest_elf,
    output: '@BASENAME@.json',
    command: [
        py3,
        parseelf.full_path(),
        '@INPUT@',
        '@OUTPUT@',
    ],
    build_by_default: true,
)

meson.add_install_script(sentry_install_script, autotest_map_file, get_option('infodir') / autotest_task_name)
