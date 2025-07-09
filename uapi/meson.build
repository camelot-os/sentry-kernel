# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if not with_uapi_opt
    subdir_done()
endif

add_languages('rust', native: false, required: true)

# Set rust toolchain config entry according to kconfig
# Note:
#   configuration_file is done at top level meson.build in order to generate
#   rust-toolchain.toml at build root directory.
rust_toolchain_in = files('rust-toolchain.toml.in')
rust_toolchain_config = configuration_data()
rust_toolchain_config.set('channel', get_option('rust-channel'))
rust_toolchain_config.set('target', kconfig_data.get_unquoted('CONFIG_RUSTC_TARGET'))

global_rust_build_args = [
    '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs),
    target_rustargs,
    '-C', 'lto=true', '-C', 'relocation-model=pic',
    '-C', 'link-args=--emit-relocs',
]

if kconfig_data.get('CONFIG_ARCH_RV32', 0) == 1
    # Ensure that unsupported extensions are deactivated in rustc
    if kconfig_data.get('CONFIG_HAS_ZMMUL', 0) != 1
        # global_rust_build_args += ['-C', 'target-feature=-zmmul']
    endif

    if kconfig_data.get('CONFIG_HAS_ZIFENCEI', 0) != 1
        # global_rust_build_args += ['-C', 'target-feature=-zifencei']
    endif
endif

rust_edition = '2024'
uapi_rust_std = 'rust_std=' + rust_edition
uapi_manifest = files('Cargo.toml')

cargo_install = get_option('with-install-crates')

subdir('include/uapi')
subdir('src')

cargo = find_program('cargo', required: true)
cargo_fmt = find_program('cargo-fmt', required: false)
cargo_clippy = find_program('cargo-clippy', required: false)
cargo_index = find_program('cargo-index', required: cargo_install)

if with_doc_opt
uapi_doc = custom_target(
    'doc-uapi',
    input: uapi_manifest,
    output: 'doc',
    command: [cargo, 'doc', '--manifest-path', '@INPUT@'],
    depend_files: [uapi_modules, uapi_libfile],
    env: {'CARGO_TARGET_DIR':meson.current_build_dir()},
    install: true,
    install_dir: get_option('datadir') / 'doc/sentry-uapi',
    install_tag: 'doc',
)

uapi_doc_alias = alias_target('doc-uapi', uapi_doc)
endif # with_doc

# Following target are format/lint check and test
# These are declared as test entry in the `uapi` test suite

if with_tests
cargo_manifest_opt = '--manifest-path=' + uapi_manifest[0].full_path()
cargo_targetdir_opt = '--target-dir=' + meson.current_build_dir()
cargo_target_opt = '--target=' + target_rust

if cargo_fmt.found()
test(
    'cargo-fmt',
    cargo_fmt,
    args: [cargo_manifest_opt, '--check' ],
    suite: 'uapi',
)
endif # cargo_fmt found

if cargo_clippy.found()
test(
    'cargo-clippy',
    cargo,
    args: [
        'clippy',
        cargo_manifest_opt,
        cargo_targetdir_opt,
        cargo_target_opt,
        '--no-deps',
        '--',
        '-Dwarnings',
    ],
    suite: 'uapi',
)
endif # cargo clippy found

test(
    'cargo-test',
    cargo,
    args: [
        'test',
        cargo_manifest_opt,
        cargo_targetdir_opt,
        '--',
        '--test-threads=1',
    ],
    is_parallel: false,
    suite: 'uapi',
)

endif #with_tests

# Install devel files for cargo
# - rust_target: llvm target triple
# - rustargs: target rustargs (compile and link flags)
rust_target_template = files('rust_target.in')
rust_target_file = configure_file(
    input: rust_target_template,
    output: '@BASENAME@',
    command: [jinja_cli, '@INPUT@', '--define', 'target', target_rust, '-o', '@OUTPUT@'],
    install: true,
    install_dir: get_option('datadir') / 'cargo',
    install_tag: 'data',
)

rustargs_template = files('rustargs.in')
rustargs_file = configure_file(
    input: rustargs_template,
    output: '@BASENAME@',
    command: [jinja_cli, '@INPUT@', '--define', 'rustargs', ' '.join(implicit_target_rustargs + target_rustargs), '-o', '@OUTPUT@'],
    install: true,
    install_dir: get_option('datadir') / 'cargo',
    install_tag: 'data',
)

summary(
    {
        'install crates': cargo_install,
    },
    section: 'Cargo',
    bool_yn: true,
)

if cargo_install
fs = import('fs')
cargo_local_registry = fs.expanduser(get_option('cargo-registry'))

if not fs.is_absolute(cargo_local_registry)
    error('cargo local registry must be an absolute path')
endif

if not fs.is_dir(cargo_local_registry)
    error('cargo local registry must exist and be a directory')
endif

cargo_local_registry_index = join_paths(cargo_local_registry, 'index')

meson.add_install_script(
    cargo,
    'index',
    'add',
    '--force',
    '--manifest-path=' + uapi_manifest[0].full_path(),
    '--index=' + cargo_local_registry_index,
    '--index-url=file://' + cargo_local_registry_index,
    '--upload=' + cargo_local_registry,
    '--',
    '--no-verify',
    install_tag: 'devel',
)

summary(
    {
        'cargo local registry': cargo_local_registry,
    },
    section: 'Cargo',
    bool_yn: true,
)

endif # with install crates

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

summary(
    {
        'rust edition': rust_edition,
    },
    section: 'Target specific compile args'
)
