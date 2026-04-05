# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

from concurrent import futures
import logging
import os
from pathlib import Path
import subprocess
import threading
from dataclasses import dataclass, field
from typing import Any
from typing import Final

import grpc

from .dispatcher import SyscallStore
from .grpc import emulator_pb2, emulator_pb2_grpc
from .protocol import ProtocolError, deserialize_request

DEFAULT_HOST: Final[str] = "127.0.0.1"
DEFAULT_PORT: Final[int] = 44044
UINT32_MAX: Final[int] = (1 << 32) - 1


@dataclass(frozen=True, slots=True)
class StartSpec:
    app_path: Path
    label: int


@dataclass(frozen=True, slots=True)
class AppContext:
    label: int
    handle: int
    app_path: Path
    process: subprocess.Popen[bytes]


def parse_start_option(value: str) -> StartSpec:
    app_part, sep, label_part = value.partition(",")
    if sep == "":
        raise ValueError("--start expects 'app.elf,label=<u32>'")

    app = app_part.strip()
    if not app:
        raise ValueError("--start application path cannot be empty")

    key, eq, raw_label = label_part.partition("=")
    if eq == "" or key.strip() != "label":
        raise ValueError("--start expects 'label=<u32>'")

    try:
        label = int(raw_label.strip(), 0)
    except ValueError as exc:
        raise ValueError("label must be an integer in [0, 4294967295]") from exc

    if label < 0 or label > UINT32_MAX:
        raise ValueError("label must be an integer in [0, 4294967295]")

    return StartSpec(app_path=Path(app), label=label)


@dataclass(slots=True)
class GrpcEmulatorDaemon:
    host: str = DEFAULT_HOST
    port: int = DEFAULT_PORT
    start_specs: tuple[StartSpec, ...] = ()
    store: SyscallStore = field(default_factory=SyscallStore)
    logger: logging.Logger = field(
        default_factory=lambda: logging.getLogger("camelot.sentry_emulator")
    )

    _bound_address: tuple[str, int] | None = field(default=None, init=False)
    _contexts_by_label: dict[int, AppContext] = field(default_factory=dict, init=False)
    _started_processes: list[subprocess.Popen[bytes]] = field(default_factory=list, init=False)
    _next_handle: int = field(default=1, init=False)

    def _allocate_handle(self) -> int:
        if self._next_handle > UINT32_MAX:
            raise RuntimeError("app context handle overflow")
        handle = self._next_handle
        self._next_handle += 1
        return handle

    def _launch_start_spec(self, spec: StartSpec) -> AppContext:
        if spec.label in self._contexts_by_label:
            raise RuntimeError(f"duplicate app label: {spec.label}")

        app_path = spec.app_path.expanduser().resolve()
        if not app_path.exists():
            raise RuntimeError(f"app does not exist: {app_path}")

        child_env = os.environ.copy()
        child_env["SENTRY_APP_LABEL"] = str(spec.label)
        child_env["SENTRY_EMULATOR_HOST"] = self.host
        child_env["SENTRY_EMULATOR_PORT"] = str(self.port)

        process = subprocess.Popen([str(app_path)], env=child_env)
        context = AppContext(
            label=spec.label,
            handle=self._allocate_handle(),
            app_path=app_path,
            process=process,
        )
        self._contexts_by_label[spec.label] = context
        self._started_processes.append(process)
        return context

    def _startup_apps(self) -> None:
        for spec in self.start_specs:
            context = self._launch_start_spec(spec)
            self.logger.info(
                "Started app label=%d handle=%d pid=%d path=%s",
                context.label,
                context.handle,
                context.process.pid,
                context.app_path,
            )

    def _terminate_started_apps(self) -> None:
        for process in self._started_processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=2)

    def context_for_label(self, label: int) -> AppContext | None:
        return self._contexts_by_label.get(label)

    @property
    def bound_address(self) -> tuple[str, int]:
        if self._bound_address is None:
            raise RuntimeError("daemon is not bound yet")
        return self._bound_address

    def serve_forever(
        self,
        stop_event: threading.Event | None = None,
        ready_event: threading.Event | None = None,
        poll_interval: float = 0.2,
    ) -> None:
        event = stop_event if stop_event is not None else threading.Event()

        self._startup_apps()

        grpc_server = grpc.server(futures.ThreadPoolExecutor(max_workers=4))
        emulator_pb2_grpc.add_EmulatorServicer_to_server(
            _EmulatorServicer(daemon=self, store=self.store, logger=self.logger), grpc_server
        )  # type: ignore[no-untyped-call]

        bound_port = grpc_server.add_insecure_port(f"{self.host}:{self.port}")
        if bound_port == 0:
            raise RuntimeError(f"cannot bind gRPC server on {self.host}:{self.port}")

        self._bound_address = (self.host, int(bound_port))
        grpc_server.start()

        if ready_event is not None:
            ready_event.set()

        self.logger.info(
            "Sentry emulator listening on grpc://%s:%d",
            self._bound_address[0],
            self._bound_address[1],
        )

        try:
            while not event.wait(timeout=poll_interval):
                continue
        finally:
            grpc_server.stop(grace=0).wait()
            self._terminate_started_apps()


@dataclass(slots=True)
class _EmulatorServicer(emulator_pb2_grpc.EmulatorServicer):
    daemon: GrpcEmulatorDaemon
    store: SyscallStore
    logger: logging.Logger

    def Dispatch(
        self, request: Any, context: grpc.ServicerContext
    ) -> Any:
        response_cls = getattr(emulator_pb2, "DispatchResponse")

        try:
            message = deserialize_request(request)
        except ProtocolError as exc:
            self.store.register_invalid()
            self.logger.warning("Rejected command from %s: %s", context.peer(), exc)
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details(str(exc))
            return response_cls(status=1, detail=str(exc))

        app_context = self.daemon.context_for_label(message.label)
        if app_context is None:
            self.store.register_invalid()
            detail = f"unknown app label: {message.label}"
            self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
            context.set_code(grpc.StatusCode.NOT_FOUND)
            context.set_details(detail)
            return response_cls(status=1, detail=detail)

        self.store.register(message)
        # Keep this trace explicit for early integration/debug phases.
        self.logger.info(
            "grpc command label=%d handle=%d syscall=%s args=%s peer=%s",
            message.label,
            app_context.handle,
            message.syscall,
            list(message.args),
            context.peer(),
        )
        return response_cls(status=0, detail="ok")
