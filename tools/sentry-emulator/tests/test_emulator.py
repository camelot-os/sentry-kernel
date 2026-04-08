# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""End-to-end emulator tests using the Rust sample applications."""

import os
import pathlib
import subprocess
import sys

import pytest

PROJECT_ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO_ROOT = PROJECT_ROOT.parents[1]
SAMPLE_RUST_BIN_DIR = (
    REPO_ROOT / "builddir" / "tools" / "sentry-emulator" / "sample-rust-target" / "debug"
)


@pytest.mark.emulator
def test_cli_starts_sample_rust_apps_via_start() -> None:
    app_one = SAMPLE_RUST_BIN_DIR / "sample-app-one"
    app_two = SAMPLE_RUST_BIN_DIR / "sample-app-two"

    missing_binaries = [str(path) for path in (app_one, app_two) if not path.exists()]
    if missing_binaries:
        pytest.skip(
            "sample Rust apps are not built in builddir: " + ", ".join(missing_binaries)
        )

    child_env = os.environ.copy()
    pythonpath_entries = [str(PROJECT_ROOT / "src")]
    existing_pythonpath = child_env.get("PYTHONPATH")
    if existing_pythonpath:
        pythonpath_entries.append(existing_pythonpath)
    child_env["PYTHONPATH"] = os.pathsep.join(pythonpath_entries)

    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "camelot.sentry_emulator",
            "--log-level",
            "INFO",
            "--start",
            f"{app_one},label=7",
            "--start",
            f"{app_two},label=8",
        ],
        cwd=PROJECT_ROOT,
        env=child_env,
        capture_output=True,
        text=True,
        timeout=15,
        check=False,
    )

    assert completed.returncode == 0, (
        f"stdout:\n{completed.stdout}\n\nstderr:\n{completed.stderr}"
    )
    assert "Started app label=7" in completed.stderr
    assert "Started app label=8" in completed.stderr
    assert "App exited label=7" in completed.stderr
    assert "App exited label=8" in completed.stderr
    assert "All startup tasks have terminated, stopping emulator daemon" in completed.stderr
    assert "Sentry emulator stopped" in completed.stderr

    # IPC path must be exercised by both sample applications.
    assert "[sample-app-one:7] send_ipc(peer): Ok" in completed.stdout
    assert "[sample-app-two:8] wait_for_event(ipc, no timeout): Ok" in completed.stdout
    assert "[sample-app-two:8] ipc event received" in completed.stdout
