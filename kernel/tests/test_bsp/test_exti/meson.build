# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 Camelot OSS Team
# SPDX-License-Identifier: Apache-2.0


test_bsp_exti_c = executable(
    'test_bsp_exti',
    sources: [
        files(
            'test_exti.c',
            join_paths(meson.project_source_root(), 'kernel/src/drivers/exti/stm32-exti.c'),
        ),
        exti_h, stm32_exti_dtsgen_h, stm32_exti_dtsgen_c,
        sentry_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    c_args: [
        '-I'+join_paths(meson.project_build_root(), 'kernel/src/drivers/exti'),
        global_build_args,
        '-DTEST_MODE=1',
    ],
    dependencies: [ cmocka_dep, cmsis_dep, mock_lib_dep ],
    native: true,
)

test('exti',
     test_bsp_exti_c,
     env: nomalloc,
     suite: 'ut-bsp')
