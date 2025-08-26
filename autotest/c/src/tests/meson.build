# SPDX-FileCopyrightText: 2023 - 2025 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

subdir('include')
subdir('src')

autotest_test_dep = declare_dependency(
    link_with: autotest_test_lib,
    include_directories: testlib_inc,
)
