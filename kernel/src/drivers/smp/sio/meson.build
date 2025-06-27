# SPDX-FileCopyrightText: 2025 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

sio_drv_sources = files(
    'cpuid.c',
    'doorbell.c',
    'fifo.c',
)

sio_prv_headers = files(
    'sio_private.h',
)

bsp_source_set.add(when: 'CONFIG_HAS_SIO', if_true: sio_drv_sources)
bsp_private_header_set.add(when: 'CONFIG_HAS_SIO', if_true: sio_prv_headers)
