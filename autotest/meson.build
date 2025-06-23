# SPDX-FileCopyrightText: 2023 - 2025 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# Set rust toolchain config entry according to kconfig
# Note:
#   configuration_file is done at top level meson.build in order to generate
#   rust-toolchain.toml at build root directory.
rust_toolchain_in = files('src/tests/src-rs/rust-toolchain.toml.in')
rust_toolchain_config = configuration_data()
rust_toolchain_config.set('channel', get_option('rust-channel'))
rust_toolchain_config.set('target', kconfig_data.get_unquoted('CONFIG_RUSTC_TARGET'))

global_rust_build_args = [
    '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs),
    target_rustargs,
    '-C', 'lto=true', '-C', 'relocation-model=pic', '-C', 'link-args=--emit-relocs'
]

if not with_autotest
    subdir_done()
endif

if meson.is_subproject()
warning('!!! Are you sure you want to build the autotest task as a subproject ?')
endif

ssmod = import('sourceset')

# local tool for easy ELF parsing to json file
parseelf = find_program('parseelf.py', required: true, dirs: [meson.project_source_root() / 'tools'])

autotest_task_name = 'autotest'

userspace_args = [
    '-fstack-protector-strong',
    '-Wconversion',
]

# populated in src
autotest_ldscript_template = files()
autotest_sourceset = ssmod.source_set()
autotest_headerset = ssmod.source_set()

subdir('include')
subdir('src')

autotest_sources = autotest_sourceset.apply(kconfig_data, strict: false).sources()
autotest_headers = autotest_headerset.apply(kconfig_data, strict: false).sources()

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

autotest_map_file = '@0@.map'.format(autotest_task_name)

uapi_inc = include_directories('../uapi/include')

autotest_elf = executable(
    autotest_task_name,
    name_suffix: 'elf',
    sources: [ autotest_sources, autotest_headers ],
    include_directories: [ uapi_inc, autotest_inc ],
    dependencies: [ autotest_test_dep ],
    c_args: [ target_arch_args, global_build_args, userspace_args ],
    link_args: [ '-lgcc', target_arch_args, autotest_linker_args, '-Wl,-Map=@0@'.format(autotest_map_file)],
    link_language: 'c',
    link_depends: [ autotest_ldscript ],
    install: true,
)

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
    ],
    build_by_default: true,
)

meson.add_install_script(sentry_install_script, autotest_map_file, get_option('infodir') / autotest_task_name)
