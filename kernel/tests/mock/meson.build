# SPDX-FileCopyrightText: 2025 Camelot OSS team
# SPDX-License-Identifier: Apache-2.0

mock_src = files(
    'src/memory.c',
    'src/garbage.c',
)

mock_hdr = files(
    'include/garbage.h',
)

mock_inc = include_directories('include')

# XXX: int-to-pointer is the consequence of keeping u32 as addr source,
# while x86_64 is 64 bits arch. Although, we need to map in a u32 memory
# domain to emulate the MCU device here
mock_lib = static_library(
    'mock',
    sources: [
        mock_src,
    ],
    include_directories: kernel_inc,
    install: false,
    c_args: [ global_build_args, '-Wno-int-to-pointer-cast' ],
    native: true,
)

# Note: there is no 'include dir' is as this is only a mocking lib
# for kernel exported API
mock_lib_dep = declare_dependency(
    link_with: mock_lib,
    include_directories: mock_inc,
)
