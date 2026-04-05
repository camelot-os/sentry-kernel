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


def test_grpc_server_receives_and_sorts_messages(
    tmp_path: pathlib.Path, capsys: pytest.CaptureFixture[str]
) -> None:
    app_path_a = tmp_path / "dummy_app_a.sh"
    app_path_a.write_text("#!/bin/sh\nwhile true; do sleep 1; done\n", encoding="utf-8")
    app_path_a.chmod(0o755)

    app_path_b = tmp_path / "dummy_app_b.sh"
    app_path_b.write_text("#!/bin/sh\nwhile true; do sleep 1; done\n", encoding="utf-8")
    app_path_b.chmod(0o755)

    daemon = GrpcEmulatorDaemon(
        host="127.0.0.1",
        port=0,
        start_specs=(
            StartSpec(app_path=app_path_a, label=7),
            StartSpec(app_path=app_path_b, label=8),
        ),
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

        stub.Dispatch(
            emulator_pb2.DispatchRequest(
                syscall="exchange_to_kernel",
                label=7,
                payload=b"hello from task",
            )
        )
        exchange_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        assert exchange_reply.payload.startswith(b"hello from task")

        stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="log", args=[15], label=7)
        )

        proc_self = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="get_process_handle", args=[7], label=7)
        )
        assert proc_self.status == 0
        self_handle_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        self_handle = int.from_bytes(self_handle_reply.payload[:4], "little")
        assert self_handle > 0

        proc_other = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="get_process_handle", args=[8], label=7)
        )
        assert proc_other.status == 0
        other_handle_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        other_handle = int.from_bytes(other_handle_reply.payload[:4], "little")
        assert other_handle > 0
        assert other_handle != self_handle

        send_sig = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="send_signal", args=[other_handle, 11], label=7)
        )
        assert send_sig.status == 0

        alarm_start = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="alarm", args=[50, 1], label=7)
        )
        assert alarm_start.status == 0
        alarm_stop = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="alarm", args=[50, 2], label=7)
        )
        assert alarm_stop.status == 0

        rnd = stub.Dispatch(emulator_pb2.DispatchRequest(syscall="get_random", label=7))
        assert rnd.status == 0
        rnd_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        assert len(rnd_reply.payload) >= 4

        cyc = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="get_cycle", args=[3], label=7)
        )
        assert cyc.status == 0
        cyc_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        assert len(cyc_reply.payload) >= 8

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

    captured = capsys.readouterr()
    assert "[app:7] hello from task" in captured.out
