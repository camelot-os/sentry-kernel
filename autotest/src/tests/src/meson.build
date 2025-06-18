# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

testlib_sourceset = ssmod.source_set()

# private header, to be used by the testlib C11 implementation only
# Their Rustic counterpart are implemented in the ../src-rc directory
testlib_sourceset.add(files(
    'test_assert.h',
    'test_log.h',
))

# testlib C11 test suites implementations
testlib_sourceset.add(when: 'CONFIG_TEST_CYCLES', if_true: files('test_cycles.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_DMA', if_true: files('test_dma.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_GPIO', if_true: files('test_gpio.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_HANDLES', if_true: files('test_handle.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_IPC', if_true: files('test_ipc.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_IRQ', if_true: files('test_irq.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_DEVICES', if_true: files('test_map.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_RANDOM', if_true: files('test_random.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_SHM', if_true: files('test_shm.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_SIGNALS', if_true: files('test_signal.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_SLEEP', if_true: files('test_sleep.c'))
testlib_sourceset.add(when: 'CONFIG_TEST_YIELD', if_true: files('test_yield.c'))

testlib_sourceset_config = testlib_sourceset.apply(kconfig_data, strict: false)

# autotest test lib, in C11
# Note: autotest_inc (that include arch-specific and drivers) is still needed as
# IRQ test suites is using HW timer for testing.
# TODO: the driver may be moved as a local implementation but this would requires
# the Rust implementation to hold a Rust driver too.
autotest_test_lib = static_library('testlib',
    sources: [
        testlib_sourceset_config.sources(),
        testlib_headerset_config.sources(),
    ],
    include_directories: [ testlib_inc, uapi_inc, autotest_inc ],
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    link_with: [ uapi_lib ],
    dependencies: [testlib_sourceset_config.dependencies(), external_deps ],
)
