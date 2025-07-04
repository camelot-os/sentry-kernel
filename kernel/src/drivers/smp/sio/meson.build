# SPDX-FileCopyrightText: 2025 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

sio_drv_sources = files(
    'cpuid.c',
)

sio_h = custom_target('gen_sio',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('sio'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'SIO',
       '@INPUT@'
    ],
)

bsp_source_set.add(sio_drv_sources)
bsp_private_header_set.add(sio_h)
