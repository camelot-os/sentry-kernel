# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


emulator_pyproject = files('pyproject.toml')
emulator_tox = files('tox.ini')

emulator_build = custom_target(
    'sentry-emulator-build',
    input: [emulator_pyproject, emulator_tox],
    output: 'sentry-emulator-build.stamp',
    command: [
        py3,
        '-c',
        'import pathlib, subprocess, sys; out = pathlib.Path(sys.argv[1]); src = pathlib.Path(sys.argv[2]); dist = pathlib.Path(sys.argv[3]); dist.mkdir(parents=True, exist_ok=True); subprocess.run([sys.executable, "-m", "build", "--sdist", "--wheel", "--outdir", str(dist), str(src)], check=True); out.write_text("ok\n", encoding="utf-8")',
        '@OUTPUT@',
        meson.current_source_dir(),
        meson.current_build_dir() / 'dist',
    ],
    build_by_default: true,
)

cargo = find_program('cargo', required: true)

sample_rust_manifest = files('sample-rust-app/Cargo.toml')

sample_rust_build = custom_target(
    'sentry-emulator-sample-rust-app-build',
    input: sample_rust_manifest,
    output: 'sentry-emulator-sample-rust-app-build.stamp',
    command: [
        py3,
        '-c',
        'import pathlib, subprocess, sys; out = pathlib.Path(sys.argv[1]); manifest = pathlib.Path(sys.argv[2]); target = pathlib.Path(sys.argv[3]); subprocess.run(["cargo", "build", "--manifest-path", str(manifest), "--target-dir", str(target)], check=True); out.write_text("ok\\n", encoding="utf-8")',
        '@OUTPUT@',
        sample_rust_manifest[0].full_path(),
        meson.current_build_dir() / 'sample-rust-target',
    ],
    build_by_default: true,
)

if with_tests
    test(
        'sentry-emulator-pytest',
        py3,
        args: [
            '-m',
            'pytest',
            '-c',
            meson.current_source_dir() / 'pyproject.toml',
            meson.current_source_dir() / 'tests',
        ],
        suite: 'tools',
        workdir: meson.current_source_dir(),
    )

    test(
        'sentry-emulator-mypy',
        py3,
        args: [
            '-m',
            'mypy',
            meson.current_source_dir() / 'src',
        ],
        suite: 'tools',
        workdir: meson.current_source_dir(),
    )
endif

summary(
    {
        'sentry emulator artifacts': meson.current_build_dir() / 'dist',
        'sentry emulator sample rust app': meson.current_build_dir() / 'sample-rust-target',
    },
    section: 'Tools',
)
