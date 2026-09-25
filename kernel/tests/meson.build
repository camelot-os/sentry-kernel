# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

add_languages('cpp', native: true, required: true)

hostcc = meson.get_compiler('c', native: true)
hostcc.has_function('__builtin_ffsl')

# no need to perturb malloc as we do not have malloc in kernel
nomalloc = environment({'MALLOC_PERTURB_': '0'})

cmocka_proj = subproject('cmocka',
                         default_options: 'c_args=-w'
)

cmocka_dep = cmocka_proj.get_variable('cmocka_native_dep')

# testing cmocka itself, with a generic test case
test_cmocka = executable(
    'test_cmocka',
    sources: [
        files('cmocka.c')
    ],
    override_options: ['c_std=gnu11'],
    c_args: [
        global_build_args,
        '-DTEST_MODE=1',
    ],
    dependencies: [ cmocka_dep ],
    native: true,
)

test('cmocka-exec',
     test_cmocka,
     env: nomalloc,
     suite: 'cmocka')

subdir('mock')
subdir('test_utils')
subdir('test_bsp')
subdir('test_managers')
