# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Internal module split for emulator server runtime."""

from .constants import (
    DEFAULT_HOST,
    DEFAULT_PORT,
    EVENT_MAGIC,
    EVENT_TYPE_SIGNAL,
    EXCHANGE_BUFFER_LEN,
    MAX_PENDING_SIGNALS,
    PRECISION_CYCLE,
    PRECISION_MICROSECONDS,
    PRECISION_MILLISECONDS,
    PRECISION_NANOSECONDS,
    SIGNAL_ABORT,
    SIGNAL_ALARM,
    SIGNAL_USR2,
    STATUS_AGAIN,
    STATUS_BUSY,
    STATUS_DENIED,
    STATUS_INVALID,
    STATUS_NO_ENTITY,
    STATUS_OK,
    STATUS_TIMEOUT,
    UINT32_MAX,
)
from .daemon import GrpcEmulatorDaemon
from .models import AlarmRegistration, AppContext, StartSpec, parse_start_option
from .servicer import EmulatorServicer

__all__ = [
    "AlarmRegistration",
    "AppContext",
    "DEFAULT_HOST",
    "DEFAULT_PORT",
    "EVENT_MAGIC",
    "EVENT_TYPE_SIGNAL",
    "EXCHANGE_BUFFER_LEN",
    "EmulatorServicer",
    "GrpcEmulatorDaemon",
    "MAX_PENDING_SIGNALS",
    "PRECISION_CYCLE",
    "PRECISION_MICROSECONDS",
    "PRECISION_MILLISECONDS",
    "PRECISION_NANOSECONDS",
    "SIGNAL_ABORT",
    "SIGNAL_ALARM",
    "SIGNAL_USR2",
    "STATUS_AGAIN",
    "STATUS_BUSY",
    "STATUS_DENIED",
    "STATUS_INVALID",
    "STATUS_NO_ENTITY",
    "STATUS_OK",
    "STATUS_TIMEOUT",
    "StartSpec",
    "UINT32_MAX",
    "parse_start_option",
]
