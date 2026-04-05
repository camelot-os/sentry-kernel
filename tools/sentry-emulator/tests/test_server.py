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

        wait_non_blocking = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="wait_for_event", args=[2, -1], label=8)
        )
        assert wait_non_blocking.status == 8

        wait_timeout = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="wait_for_event", args=[2, 25], label=8)
        )
        assert wait_timeout.status == 7

        send_sig = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="send_signal", args=[other_handle, 11], label=7)
        )
        assert send_sig.status == 0

        wait_result: dict[str, object] = {}

        def wait_for_signal() -> None:
            with grpc.insecure_channel(
                f"{daemon.bound_address[0]}:{daemon.bound_address[1]}"
            ) as wait_channel:
                wait_stub = emulator_pb2_grpc.EmulatorStub(wait_channel)
                wait_result["response"] = wait_stub.Dispatch(
                    emulator_pb2.DispatchRequest(
                        syscall="wait_for_event",
                        args=[2, 1000],
                        label=8,
                    )
                )
                wait_result["exchange"] = wait_stub.Dispatch(
                    emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=8)
                )

        waiter = threading.Thread(target=wait_for_signal, daemon=True)
        waiter.start()
        time.sleep(0.05)

        send_sig_wait = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="send_signal", args=[other_handle, 11], label=7)
        )
        assert send_sig_wait.status == 0
        waiter.join(timeout=2.0)
        assert not waiter.is_alive()
        assert "response" in wait_result
        assert "exchange" in wait_result
        assert wait_result["response"].status == 0
        event_payload = wait_result["exchange"].payload
        assert event_payload[0] == 2
        assert int.from_bytes(event_payload[2:4], "little") == 0x4242
        assert int.from_bytes(event_payload[4:8], "little") == self_handle
        assert int.from_bytes(event_payload[8:12], "little") == 11

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
    assert "[dummy_app_a:7] hello from task" in captured.out


def test_exit_deactivates_context_and_stops_daemon(tmp_path: pathlib.Path) -> None:
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

        exit_first = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exit", args=[0], label=7)
        )
        assert exit_first.status == 0
        assert exit_first.detail == "context deactivated"

        with pytest.raises(grpc.RpcError):
            stub.Dispatch(emulator_pb2.DispatchRequest(syscall="map_dev", args=[10], label=7))

        exit_second = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exit", args=[0], label=8)
        )
        assert exit_second.status == 0
        assert exit_second.detail == "all tasks exited"

    thread.join(timeout=2.0)
    assert not thread.is_alive()


def test_wait_for_event_blocking_wakes_on_signal(tmp_path: pathlib.Path) -> None:
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

        sender_self = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="get_process_handle", args=[7], label=7)
        )
        assert sender_self.status == 0
        sender_self_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        sender_handle = int.from_bytes(sender_self_reply.payload[:4], "little")
        assert sender_handle > 0

        target_lookup = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="get_process_handle", args=[8], label=7)
        )
        assert target_lookup.status == 0
        target_reply = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=7)
        )
        target_handle = int.from_bytes(target_reply.payload[:4], "little")
        assert target_handle > 0
        assert target_handle != sender_handle

        wait_result: dict[str, object] = {}

        def wait_blocking() -> None:
            with grpc.insecure_channel(
                f"{daemon.bound_address[0]}:{daemon.bound_address[1]}"
            ) as wait_channel:
                wait_stub = emulator_pb2_grpc.EmulatorStub(wait_channel)
                wait_result["response"] = wait_stub.Dispatch(
                    emulator_pb2.DispatchRequest(
                        syscall="wait_for_event",
                        args=[2, 0],
                        label=8,
                    )
                )
                wait_result["exchange"] = wait_stub.Dispatch(
                    emulator_pb2.DispatchRequest(syscall="exchange_from_kernel", label=8)
                )

        waiter = threading.Thread(target=wait_blocking, daemon=True)
        waiter.start()
        time.sleep(0.05)
        assert waiter.is_alive()

        send_sig = stub.Dispatch(
            emulator_pb2.DispatchRequest(syscall="send_signal", args=[target_handle, 11], label=7)
        )
        assert send_sig.status == 0

        waiter.join(timeout=2.0)
        assert not waiter.is_alive()
        assert "response" in wait_result
        assert "exchange" in wait_result

        response = wait_result["response"]
        exchange = wait_result["exchange"]
        assert response.status == 0
        payload = exchange.payload
        assert payload[0] == 2
        assert payload[1] == 4
        assert int.from_bytes(payload[2:4], "little") == 0x4242
        assert int.from_bytes(payload[4:8], "little") == sender_handle
        assert int.from_bytes(payload[8:12], "little") == 11

    stop_event.set()
    thread.join(timeout=2.0)
    assert not thread.is_alive()
