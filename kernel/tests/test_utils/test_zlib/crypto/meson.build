# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

sha256_nist_vectors_dir = meson.current_source_dir() / 'vectors'

sha256_nist_test = executable(
    'test_zlib_sha256_nist',
    sources: [
        files('test_sha256_nist.c'),
        files('sha256_nist_parser.c'),
        files('../../../../src/zlib/string.c'),
        files('../../../../src/zlib/crypto/sha-256.c'),
        sentry_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    c_args: [
        '-DTEST_MODE=1',
        '-Wno-pedantic',
        '-DCONFIG_SECU_METADATA_SHA256_CHECK=1',
        '-DNIST_SHA256_VECTOR_DIR="' + sha256_nist_vectors_dir + '"',
    ],
    dependencies: [ cmocka_dep, mock_lib_dep ],
    native: true,
)

test(
    'zlib-sha256-nist',
    sha256_nist_test,
    env: nomalloc,
    suite: 'ut-utils',
)
