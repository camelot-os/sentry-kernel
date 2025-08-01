# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

testlib_inc = include_directories('.')

testlib_headerset = ssmod.source_set()

# adding test suites interface
testlib_headerset.add(
    files(
        'test_cycles.h',
        'test_dma.h',
        'test_gpio.h',
        'test_handle.h',
        'test_ipc.h',
        'test_irq.h',
        'test_map.h',
        'test_random.h',
        'test_shm.h',
        'test_signal.h',
        'test_sleep.h',
        'test_yield.h',
    )
)


# the test library required device config when tested
devices_template_h = files(['devices-dt.h.in'])
devices_dtsgen_h = dtsgen.process(devices_template_h)

shm_template_h = files(['shms-dt.h.in'])
shm_dtsgen_h = dtsgen.process(shm_template_h)

# adding generated dts-based content only if they are defined
testlib_headerset.add(when: 'CONFIG_TEST_DEVICES', if_true: devices_dtsgen_h)
testlib_headerset.add(when: 'CONFIG_TEST_SHM', if_true: shm_dtsgen_h)

testlib_headerset_config = testlib_headerset.apply(kconfig_data, strict: false)
