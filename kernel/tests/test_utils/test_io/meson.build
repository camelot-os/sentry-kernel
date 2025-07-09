# SPDX-FileCopyrightText: 2025 Camelot OSS Team
# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_io = executable(
    'test_io',
    sources: [ files('test_io.c'), sentry_header_set_config.sources() ],
    include_directories: kernel_inc,
    c_args: [ '-DTEST_MODE=1', '-Wno-pedantic' ],
    dependencies: [cmocka_dep, mock_lib_dep ],
    native: true,
)

test('io',
     test_io,
     env: nomalloc,
     suite: 'ut-utils')
