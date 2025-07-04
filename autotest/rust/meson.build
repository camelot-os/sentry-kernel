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

devices_dtsgen_rs = []

if kconfig_data.get('CONFIG_TEST_DEVICES', 0) == 1
devices_template_rs = files(['src/devices_dt.rs.in'])

devices_dtsgen_rs = custom_target('devices_dtsgen_rs_gen',
    input: devices_template_rs,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)
endif

autotest_elf = executable(
    autotest_task_name,
    name_suffix: 'elf',
    sources: structured_sources(
        [
            'src/main.rs',
            'src/print.rs',
        ],
        {
            'tests': [
                'src/tests/mod.rs',
                'src/tests/log.rs',
                'src/tests/test_random.rs',
                'src/tests/test_yield.rs',
                'src/tests/test_signal.rs',
                'src/tests/test_cycles.rs',
                'src/tests/test_sleep.rs',
                'src/tests/test_ipc.rs',
                'src/tests/test_gpio.rs',
                'src/tests/devices_utils.rs',
                devices_dtsgen_rs,
            ]
        },
    ),
    rust_args: [
        autotest_rust_build_args,
    ],
    link_language: 'rust',
    link_whole: [ uapi_rlib ],
    install: true,
)
