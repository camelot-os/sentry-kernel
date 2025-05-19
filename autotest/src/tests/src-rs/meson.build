# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

testlib_rust_sourceset = ssmod.source_set()

# lib.rs must be called
testlib_rust_sourceset.add(files('src/lib.rs'))

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

autotest_test_rustlib = static_library('testlib_rust',
    sources: testlib_rust_sourceset_config.sources(),
    rust_abi: 'none',
    rust_args: [
        '--crate-type=lib',
        '--target=thumbv8m.main-none-eabihf',  # or chosen target instead
    ] + global_rust_build_args,
    override_options: ["rust_std=disabled"],
    extra_files: uapi_modules,
    install: false,
)
