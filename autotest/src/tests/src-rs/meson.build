# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

testlib_rust_sourceset = ssmod.source_set()

devices_template_rs = files(['src/devices-dt.rs.in'])
devices_dtsgen_rs = dtsgen.process(devices_template_rs)

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

if kconfig_data.get('CONFIG_TEST_DEVICES', 0) == 1
    structured_src = structured_sources(
        testlib_rust_sourceset_config.sources(),
        {
            'devices': devices_dtsgen_rs,
        }
    )
else
    structured_src = structured_sources(
        testlib_rust_sourceset_config.sources(),
    )
endif

autotest_test_lib = static_library('testlib_rust',
    sources: structured_src,
    rust_abi: 'c',
    rust_args: [
        global_rust_build_args,
        '--extern', 'sentry_uapi=' + uapi_lib.full_path(),
    ],
    override_options: [uapi_rust_std],
    link_with: [uapi_rlib],
    install: false,
)
