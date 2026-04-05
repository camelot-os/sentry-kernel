# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


from importlib.metadata import PackageNotFoundError, version

from .dispatcher import SyscallStore
from .protocol import ProtocolError, SyscallMessage, deserialize_request
from .server import GrpcEmulatorDaemon

try:
    __version__ = version("camelot.sentry-emulator")
except PackageNotFoundError:
    __version__ = "0.0.0+dev"

__all__ = [
    "ProtocolError",
    "SyscallMessage",
    "SyscallStore",
    "GrpcEmulatorDaemon",
    "deserialize_request",
]
