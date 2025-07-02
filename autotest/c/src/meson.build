# SPDX-FileCopyrightText: 2023 - 2025 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# note: to avoid printf implementation redundancy, the kernel lexer for debug
# print mode is used as-is

# autotest entrypoint and basic utilities
autotest_sourceset.add(
    files(
        'main.c',
        'printf.c',
        'ssp.c',
        '../../kernel/src/managers/debug/log_lexer.c',
    )
)

subdir('arch')
subdir('drivers')

# autotest library, in C
subdir('tests')
