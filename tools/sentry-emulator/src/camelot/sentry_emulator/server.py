# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Backward-compatible public server API for the emulator.

The implementation is split into ``camelot.sentry_emulator.emulator_server``
submodules to keep concerns isolated and source files manageable.
"""

from .emulator_server import (
    DEFAULT_HOST,
    DEFAULT_PORT,
    EXCHANGE_BUFFER_LEN,
    GrpcEmulatorDaemon,
    StartSpec,
    parse_start_option,
)

__all__ = [
    "DEFAULT_HOST",
    "DEFAULT_PORT",
    "EXCHANGE_BUFFER_LEN",
    "GrpcEmulatorDaemon",
    "StartSpec",
    "parse_start_option",
]
