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
    """Bookkeeping for one active alarm registration.

    Attributes
    ----------
    delay_ms : int
        Alarm delay in milliseconds used as identifier in app context maps.
    periodic : bool
        Whether the alarm is automatically re-scheduled after firing.
    timer : threading.Timer
        Live timer object that triggers the alarm callback.
    """

    delay_ms: int
    periodic: bool
    timer: threading.Timer


@dataclass(frozen=True, slots=True)
class StartSpec:
    """Definition of one application to start with the daemon.

    Attributes
    ----------
    app_path : Path
        Executable path launched during daemon startup.
    label : int
        Application label advertised to the app runtime via environment.
    """

    app_path: Path
    label: int


@dataclass(slots=True)
class PendingIPC:
    """One in-flight IPC transfer waiting to be consumed by target.

    Attributes
    ----------
    source_handle : int
        Sender process handle.
    payload : bytes
        Copied payload emitted by sender from its exchange buffer.
    completion_status : int | None
        Final status returned to sender once delivery is resolved.
    done : threading.Event
        Event set when the transfer is consumed or aborted.
    """

    source_handle: int
    payload: bytes
    completion_status: int | None = None
    done: threading.Event = field(default_factory=threading.Event)


@dataclass(slots=True)
class AppContext:
    """Runtime context associated with one started application.

    Attributes
    ----------
    label : int
        Application label used by syscall requests.
    handle : int
        Stable process handle exposed by ``get_process_handle``.
    app_path : Path
        Executable path associated with this runtime context.
    process : subprocess.Popen[bytes] | None
        Child process instance once started, otherwise ``None``.
    exchange_buffer : bytearray
        Shared 128-byte payload area used by exchange syscalls.
    pending_signals : list[tuple[int, int]]
        FIFO queue of ``(signal, source_handle)`` waiting to be consumed.
    pending_ipcs : list[PendingIPC]
        FIFO queue of IPC transfers waiting to be consumed.
    alarms : dict[int, AlarmRegistration]
        Registered alarms keyed by delay in milliseconds.
    event_condition : threading.Condition
        Condition variable used to wake waiters when new events arrive.
    exit_code : int | None
        Exit code captured when the context is deactivated.
    """

    label: int
    handle: int
    app_path: Path
    process: subprocess.Popen[bytes] | None = None
    exchange_buffer: bytearray = field(
        default_factory=lambda: bytearray(EXCHANGE_BUFFER_LEN)
    )
    pending_signals: list[tuple[int, int]] = field(default_factory=list)
    pending_ipcs: list[PendingIPC] = field(default_factory=list)
    alarms: dict[int, AlarmRegistration] = field(default_factory=dict)
    event_condition: threading.Condition = field(default_factory=threading.Condition)
    exit_code: int | None = None

    @property
    def app_name(self) -> str:
        """Return a stable display name for daemon-emitted app logs.

        Returns
        -------
        str
            Stem of ``app_path`` when available, otherwise full filename.
        """
        return self.app_path.stem or self.app_path.name


def parse_start_option(value: str) -> StartSpec:
    """Parse one ``--start`` argument value (``APP_PATH,label=<u32>``).

    Parameters
    ----------
    value : str
        Raw CLI value passed to ``--start``.

    Returns
    -------
    StartSpec
        Validated startup specification used by the daemon.

    Raises
    ------
    ValueError
        If format is invalid, app path is empty, or label is outside ``u32``.
    """
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
