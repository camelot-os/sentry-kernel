# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

zlib_files += files(
  'crc32.c',
  'pgc32.c',
)

if kconfig_data.has('CONFIG_SECU_METADATA_SHA256_CHECK')
  zlib_files += files('sha-256.c')
endif
