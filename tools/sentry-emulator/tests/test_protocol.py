# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


import pathlib
import sys

import pytest

PROJECT_ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC_DIR = PROJECT_ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))

from camelot.sentry_emulator.grpc import emulator_pb2
from camelot.sentry_emulator.protocol import ProtocolError, deserialize_request


def test_deserialize_request_ok() -> None:
    message = deserialize_request(
        emulator_pb2.DispatchRequest(
            syscall="map_dev", args=[1, 2, 3], label=17, payload=b"abc"
        )
    )

    assert message.syscall == "map_dev"
    assert message.args == (1, 2, 3)
    assert message.label == 17
    assert message.payload == b"abc"


def test_deserialize_request_rejects_empty_syscall() -> None:
    with pytest.raises(ProtocolError):
        deserialize_request(emulator_pb2.DispatchRequest(syscall="  ", args=[12], label=1))
