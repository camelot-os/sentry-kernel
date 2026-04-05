# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .grpc import emulator_pb2


class ProtocolError(ValueError):
    """Raised when a gRPC request does not follow the emulator protocol."""


@dataclass(frozen=True, slots=True)
class SyscallMessage:
    syscall: str
    args: tuple[int, ...]
    label: int


def deserialize_request(request: Any) -> SyscallMessage:
    syscall = request.syscall.strip()
    if not syscall:
        raise ProtocolError("'syscall' must be a non-empty string")

    return SyscallMessage(
        syscall=syscall,
        args=tuple(int(arg) for arg in request.args),
        label=int(request.label),
    )
