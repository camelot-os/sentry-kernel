# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0


autotest_rust_build_args = [
    '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs),
    target_rustargs,
    '-Clink-args=-T' + autotest_ldscript.full_path(),
    '-Clink-args=-Wl,-Map=@0@'.format(autotest_map_file),
    '-Ctarget-feature=+strict-align',
    '-C', 'lto=true',
]

autotest_elf = executable(
    autotest_task_name,
    name_suffix: 'elf',
    sources: [ 'src/main.rs' ],
    rust_args: [
        autotest_rust_build_args,
    ],
    link_language: 'rust',
    link_whole: [ uapi_rlib ],
    install: true,
)
