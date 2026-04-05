# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Protocol decoding and validation utilities for emulator gRPC messages."""

from dataclasses import dataclass
from typing import Any

from .grpc import emulator_pb2


class ProtocolError(ValueError):
    """Error raised when a request does not follow emulator protocol rules."""


@dataclass(frozen=True, slots=True)
class SyscallMessage:
    """Normalized syscall request extracted from gRPC payload.

    Attributes
    ----------
    syscall : str
        Name of the syscall to emulate.
    args : tuple[int, ...]
        Positional syscall arguments as signed integers.
    label : int
        Caller application label (expected to fit in ``u32``).
    """

    syscall: str
    args: tuple[int, ...]
    label: int


def deserialize_request(request: Any) -> SyscallMessage:
    """Convert a gRPC ``DispatchRequest`` into a validated syscall message.

    Parameters
    ----------
    request : Any
        Incoming protobuf request object. It must expose ``syscall``, ``args``
        and ``label`` attributes.

    Returns
    -------
    SyscallMessage
        Immutable normalized representation used by the daemon core.

    Raises
    ------
    ProtocolError
        If ``syscall`` is empty or contains only whitespace.
    """
    syscall = request.syscall.strip()
    if not syscall:
        raise ProtocolError("'syscall' must be a non-empty string")

    return SyscallMessage(
        syscall=syscall,
        args=tuple(int(arg) for arg in request.args),
        label=int(request.label),
    )
