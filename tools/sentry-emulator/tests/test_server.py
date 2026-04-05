# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


import pathlib
import importlib
import threading
import time

import grpc
import pytest

PROJECT_ROOT = pathlib.Path(__file__).resolve().parents[1]

emulator_pb2 = importlib.import_module(
    "camelot.sentry_emulator.grpc.emulator_pb2"
)
emulator_pb2_grpc = importlib.import_module(
    "camelot.sentry_emulator.grpc.emulator_pb2_grpc"
)
GrpcEmulatorDaemon = importlib.import_module(
    "camelot.sentry_emulator.server"
).GrpcEmulatorDaemon
StartSpec = importlib.import_module("camelot.sentry_emulator.server").StartSpec
parse_start_option = importlib.import_module("camelot.sentry_emulator.server").parse_start_option



def test_parse_start_option_ok() -> None:
    spec = parse_start_option("./app.elf,label=123")

    assert str(spec.app_path) == "app.elf"
    assert spec.label == 123


def test_parse_start_option_rejects_bad_label() -> None:
    with pytest.raises(ValueError):
        parse_start_option("./app.elf,label=50000000000")


def test_grpc_server_receives_and_sorts_messages(tmp_path: pathlib.Path) -> None:
    app_path = tmp_path / "dummy_app.sh"
    app_path.write_text("#!/bin/sh\nwhile true; do sleep 1; done\n", encoding="utf-8")
    app_path.chmod(0o755)

    daemon = GrpcEmulatorDaemon(
        host="127.0.0.1",
        port=0,
        start_specs=(StartSpec(app_path=app_path, label=7),),
    )
    stop_event = threading.Event()
    ready_event = threading.Event()

    thread = threading.Thread(
        target=daemon.serve_forever,
        kwargs={"stop_event": stop_event, "ready_event": ready_event, "poll_interval": 0.05},
        daemon=True,
    )
    thread.start()

    assert ready_event.wait(timeout=2.0)

    with grpc.insecure_channel(
        f"{daemon.bound_address[0]}:{daemon.bound_address[1]}"
    ) as channel:
        stub = emulator_pb2_grpc.EmulatorStub(channel)
        stub.Dispatch(emulator_pb2.DispatchRequest(syscall="map_dev", args=[10], label=7))
        stub.Dispatch(emulator_pb2.DispatchRequest(syscall="map_dev", args=[11], label=7))
        stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="gpio_set", args=[12, 3, 1], label=7)
        )

        with pytest.raises(grpc.RpcError):
            stub.Dispatch(emulator_pb2.DispatchRequest(syscall="", args=[1], label=7))

        with pytest.raises(grpc.RpcError):
            stub.Dispatch(emulator_pb2.DispatchRequest(syscall="map_dev", args=[1], label=99))

    deadline = time.time() + 2.0
    while time.time() < deadline:
        if daemon.store.count_for("map_dev") == 2 and daemon.store.count_for("gpio_set") == 1:
            break
        time.sleep(0.02)

    stop_event.set()
    thread.join(timeout=2.0)

    assert daemon.store.count_for("map_dev") == 2
    assert daemon.store.count_for("gpio_set") == 1
    assert daemon.store.invalid_packets == 2
