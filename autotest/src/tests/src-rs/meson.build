# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

testlib_rust_sourceset = ssmod.source_set()
#autotest_libfile = files('src/lib.rs')

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
    '-C', 'lto=true', '-C', 'relocation-model=pic', '-C', 'link-args=--emit-relocs'
]
rust_edition = '2024'
autotest_rust_std = 'rust_std=' + rust_edition

devices_template_rs = files(['devices_dt.rs.in'])

devices_dtsgen_rs = custom_target('devices_dtsgen_rs_gen',
    input: devices_template_rs,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

testlib_rust_sourceset.add(
    files(
        'src/test_log.rs',
        'src/test_handle.rs',
        'src/devices_utils.rs',
        )
)

# Depends on configs in Kconfig
testlib_rust_sourceset.add(when: 'CONFIG_TEST_CYCLES', if_true: files('src/test_cycles.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_DMA', if_true: files('src/test_dma.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_GPIO', if_true: files('src/test_gpio.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_IPC', if_true: files('src/test_ipc.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_IRQ', if_true: files('src/test_irq.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_DEVICES', if_true: files('src/test_map.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_RANDOM', if_true: files('src/test_random.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_SHM', if_true: files('src/test_shm.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_SIGNALS', if_true: files('src/test_signal.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_SLEEP', if_true: files('src/test_sleep.rs'))
testlib_rust_sourceset.add(when: 'CONFIG_TEST_YIELD', if_true: files('src/test_yield.rs'))

# Apply Kconfig options
testlib_rust_sourceset_config = testlib_rust_sourceset.apply(kconfig_data, strict: false)

autotest_test_lib = static_library('testlib_rust',
    structured_sources(
            [
                'src/lib.rs',
                testlib_rust_sourceset_config.sources(),
                devices_dtsgen_rs,
            ],
    ),
    rust_abi: 'c',
    rust_args: [
        global_rust_build_args,
        '--extern', 'sentry_uapi=' + uapi_lib.full_path(),
        '--extern', 'kconfig=' + meson.source_root() / 'subprojects' / 'kconfig' / 'rust' / 'kconfig',
        '--extern', 'kconfig_import=' + meson.source_root() / 'subprojects' / 'kconfig' / 'rust' / 'kconfig_import',
    ],
    override_options: [autotest_rust_std],
    #link_with: [uapi_rlib, kconfig, kconfig_import],
    link_with: [uapi_rlib],
    install: false,
)
