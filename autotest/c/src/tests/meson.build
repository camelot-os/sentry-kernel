# SPDX-FileCopyrightText: 2023 - 2025 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab OSS Team
# SPDX-License-Identifier: Apache-2.0

# test library. The exported C11 interface is made in order to be
# implemented in C11 (in src dir) or in rust (in src-rs dir).
subdir('include')

if kconfig_data.get('CONFIG_AUTOTEST_TESTLIB_C', 0) == 1
# C11 implementation
subdir('src')
else
# Rust implementation
subdir('src-rs')
endif


# test library, to be used as C or Rust implementation of the test suite interface
# The C11 interface to autotest entrypoint is kept unique through the include/ directory
# headers.
# The Rust FFI-C must declare symbols that matches these headers prototypes
# the autotest test dependency declaration is homogeneous whatever the language used, as
# both C and Rust subdirs declare a library object of the same name, denoted autotest_test_lib.
# Here, only the C11 exported interface is declared, as autotest entrypoint is in C
autotest_test_dep = declare_dependency(
    link_with: autotest_test_lib,
    include_directories: testlib_inc,
)
