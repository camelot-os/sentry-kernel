# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if not with_tools
    subdir_done()
endif

subdir('robot')
subdir('genmetadata')

if get_option('with_emulator')
    subdir('sentry-emulator')
endif
