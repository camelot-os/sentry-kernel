# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Core data models for emulator startup and app runtime contexts."""

from dataclasses import dataclass, field
from pathlib import Path
import subprocess
import threading

from .constants import EXCHANGE_BUFFER_LEN, UINT32_MAX


@dataclass(slots=True)
class AlarmRegistration:
    delay_ms: int
    periodic: bool
    timer: threading.Timer


@dataclass(frozen=True, slots=True)
class StartSpec:
    """Definition of one application to start with the daemon."""

    app_path: Path
    label: int


@dataclass(slots=True)
class AppContext:
    """Runtime context associated with one started application."""

    label: int
    handle: int
    app_path: Path
    process: subprocess.Popen[bytes] | None = None
    exchange_buffer: bytearray = field(
        default_factory=lambda: bytearray(EXCHANGE_BUFFER_LEN)
    )
    pending_signals: list[tuple[int, int]] = field(default_factory=list)
    alarms: dict[int, AlarmRegistration] = field(default_factory=dict)
    event_condition: threading.Condition = field(default_factory=threading.Condition)
    exit_code: int | None = None

    @property
    def app_name(self) -> str:
        """Return a stable display name for daemon-emitted app logs."""
        return self.app_path.stem or self.app_path.name


def parse_start_option(value: str) -> StartSpec:
    """Parse one ``--start`` argument value (``APP_PATH,label=<u32>``)."""
    app_part, sep, label_part = value.partition(",")
    if sep == "":
        raise ValueError("--start expects 'app.elf,label=<u32>'")

    app = app_part.strip()
    if not app:
        raise ValueError("--start application path cannot be empty")

    key, eq, raw_label = label_part.partition("=")
    if eq == "" or key.strip() != "label":
        raise ValueError("--start expects 'label=<u32>'")

    try:
        label = int(raw_label.strip(), 0)
    except ValueError as exc:
        raise ValueError("label must be an integer in [0, 4294967295]") from exc

    if label < 0 or label > UINT32_MAX:
        raise ValueError("label must be an integer in [0, 4294967295]")

    return StartSpec(app_path=Path(app), label=label)
