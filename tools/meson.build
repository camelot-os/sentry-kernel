# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if not with_tools
    subdir_done()
endif

subdir('robot')
subdir('genmetadata')

if get_option('with_emulator')
    subdir('sentry-emulator')

    emulator_start_app_one = '@0@,label=7'.format(sample_rust_app_one_path)
    emulator_start_app_two = '@0@,label=8'.format(sample_rust_app_two_path)

    test(
        'sentry-emulator-rust-apps-e2e',
        py3,
        args: [
            '-m',
            'camelot.sentry_emulator',
            '--log-level',
            'INFO',
            '--start',
            emulator_start_app_one,
            '--start',
            emulator_start_app_two,
        ],
        env: {'PYTHONPATH': meson.project_source_root() / 'tools/sentry-emulator/src'},
        suite: 'emulator',
        timeout: 30,
        depends: [sample_rust_build],
    )
endif
