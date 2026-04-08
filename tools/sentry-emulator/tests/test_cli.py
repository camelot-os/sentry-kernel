# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""CLI behavior tests for argument validation and error reporting."""

import logging
import sys

from camelot.sentry_emulator import cli


def test_parser_accepts_multiple_start_arguments() -> None:
    """Repeated --start options should be collected in order."""
    parser = cli._build_parser()

    args = parser.parse_args(
        [
            "--start",
            "sample-app-one,label=7",
            "--start",
            "sample-app-two,label=8",
        ]
    )

    assert args.start == [
        "sample-app-one,label=7",
        "sample-app-two,label=8",
    ]


def test_main_returns_non_zero_and_logs_error_on_invalid_port(
    monkeypatch, caplog
) -> None:
    """Invalid port should produce ERROR log and non-zero return code."""
    monkeypatch.setattr(
        sys,
        "argv",
        ["sentry-emulator", "--log-level", "ERROR", "--port", "70000"],
    )

    caplog.set_level(logging.ERROR, logger="camelot.sentry_emulator")
    rc = cli.main()

    assert rc != 0
    assert any(
        rec.levelno == logging.ERROR and "Invalid --port value" in rec.getMessage()
        for rec in caplog.records
    )


def test_main_returns_non_zero_and_logs_error_on_invalid_start_arg(
    monkeypatch, caplog
) -> None:
    """Malformed --start should produce ERROR log and non-zero return code."""
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "sentry-emulator",
            "--log-level",
            "ERROR",
            "--start",
            "sample-app-without-label",
        ],
    )

    caplog.set_level(logging.ERROR, logger="camelot.sentry_emulator")
    rc = cli.main()

    assert rc != 0
    assert any(
        rec.levelno == logging.ERROR and "Invalid startup argument" in rec.getMessage()
        for rec in caplog.records
    )
