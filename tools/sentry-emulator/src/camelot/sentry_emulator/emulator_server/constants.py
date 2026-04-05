# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Constants used by the emulator daemon and gRPC servicer."""

from typing import Final

DEFAULT_HOST: Final[str] = "127.0.0.1"
DEFAULT_PORT: Final[int] = 44044
UINT32_MAX: Final[int] = (1 << 32) - 1
EXCHANGE_BUFFER_LEN: Final[int] = 128
SIGNAL_ABORT: Final[int] = 1
EVENT_TYPE_SIGNAL: Final[int] = 2
SIGNAL_USR2: Final[int] = 12
SIGNAL_ALARM: Final[int] = 2
EVENT_MAGIC: Final[int] = 0x4242
PRECISION_CYCLE: Final[int] = 0
PRECISION_NANOSECONDS: Final[int] = 1
PRECISION_MICROSECONDS: Final[int] = 2
PRECISION_MILLISECONDS: Final[int] = 3

STATUS_OK: Final[int] = 0
STATUS_INVALID: Final[int] = 1
STATUS_DENIED: Final[int] = 2
STATUS_NO_ENTITY: Final[int] = 3
STATUS_BUSY: Final[int] = 4
STATUS_TIMEOUT: Final[int] = 7
STATUS_AGAIN: Final[int] = 8

MAX_PENDING_SIGNALS: Final[int] = 32
