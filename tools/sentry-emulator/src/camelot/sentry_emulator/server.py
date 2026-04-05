# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""gRPC server implementation for the Sentry userspace emulator.

The daemon accepts gRPC syscall dispatch requests, validates payloads,
associates them with startup-managed application contexts, and records calls in
an in-memory store.
"""

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
EXCHANGE_BUFFER_LEN: Final[int] = 128


@dataclass(frozen=True, slots=True)
class StartSpec:
    """Definition of one application to start with the daemon.

    Attributes
    ----------
    app_path : Path
        Executable path to start.
    label : int
        Application label used to route incoming syscall requests.
    """

    app_path: Path
    label: int


@dataclass(frozen=True, slots=True)
class AppContext:
    """Runtime context associated with one started application.

    Attributes
    ----------
    label : int
        Static application label used by requests.
    handle : int
        Unique ``u32`` handle allocated by the daemon.
    app_path : Path
        Resolved executable path used to spawn the process.
    process : subprocess.Popen[bytes]
        Spawned process object for lifecycle management.
    exchange_buffer : bytearray
        Per-application exchange zone content.
    """

    label: int
    handle: int
    app_path: Path
    process: subprocess.Popen[bytes]
    exchange_buffer: bytearray = field(
        default_factory=lambda: bytearray(EXCHANGE_BUFFER_LEN)
    )


def parse_start_option(value: str) -> StartSpec:
    """Parse one ``--start`` argument value.

    Parameters
    ----------
    value : str
        Argument value formatted as ``APP_PATH,label=<u32>``.

    Returns
    -------
    StartSpec
        Parsed startup specification.

    Raises
    ------
    ValueError
        If the format is invalid or label is out of ``u32`` range.
    """
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
    """Lifecycle manager for the emulator gRPC daemon.

    Parameters
    ----------
    host : str, optional
        Interface to bind for gRPC service.
    port : int, optional
        Port to bind for gRPC service (``0`` allows dynamic allocation).
    start_specs : tuple[StartSpec, ...], optional
        Startup application specifications to spawn before serving.
    store : SyscallStore, optional
        In-memory syscall storage backend.
    logger : logging.Logger, optional
        Logger used for daemon diagnostics.
    """

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
        """Allocate the next unique context handle.

        Returns
        -------
        int
            Newly allocated ``u32`` handle.

        Raises
        ------
        RuntimeError
            If ``u32`` handle space is exhausted.
        """
        if self._next_handle > UINT32_MAX:
            raise RuntimeError("app context handle overflow")
        handle = self._next_handle
        self._next_handle += 1
        return handle

    def _launch_start_spec(self, spec: StartSpec) -> AppContext:
        """Start one app and register its runtime context.

        Parameters
        ----------
        spec : StartSpec
            Startup specification to execute.

        Returns
        -------
        AppContext
            Registered context for the started app.

        Raises
        ------
        RuntimeError
            If the label is duplicated or executable path is invalid.
        """
        if spec.label in self._contexts_by_label:
            self.logger.error("Duplicate startup label detected: %d", spec.label)
            raise RuntimeError(f"duplicate app label: {spec.label}")

        app_path = spec.app_path.expanduser().resolve()
        if not app_path.exists():
            self.logger.error("Startup executable does not exist: %s", app_path)
            raise RuntimeError(f"app does not exist: {app_path}")

        child_env = os.environ.copy()
        child_env["SENTRY_APP_LABEL"] = str(spec.label)
        child_env["SENTRY_EMULATOR_HOST"] = self.host
        child_env["SENTRY_EMULATOR_PORT"] = str(self.port)

        try:
            process = subprocess.Popen([str(app_path)], env=child_env)
        except OSError as exc:
            self.logger.error("Cannot start app label=%d path=%s: %s", spec.label, app_path, exc)
            raise RuntimeError(f"cannot start app: {app_path}") from exc

        context = AppContext(
            label=spec.label,
            handle=self._allocate_handle(),
            app_path=app_path,
            process=process,
        )
        self._contexts_by_label[spec.label] = context
        self._started_processes.append(process)
        self.logger.debug(
            "Registered app context label=%d handle=%d pid=%d",
            context.label,
            context.handle,
            context.process.pid,
        )
        return context

    def _startup_apps(self) -> None:
        """Start and register all configured startup applications."""
        if not self.start_specs:
            self.logger.info("No startup tasks configured")
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
        """Terminate all child processes started by the daemon."""
        for process in self._started_processes:
            if process.poll() is None:
                self.logger.debug("Stopping child process pid=%d", process.pid)
                process.terminate()
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    self.logger.warning(
                        "Child process pid=%d did not stop gracefully, killing",
                        process.pid,
                    )
                    process.kill()
                    process.wait(timeout=2)

    def context_for_label(self, label: int) -> AppContext | None:
        """Look up the runtime context bound to a label.

        Parameters
        ----------
        label : int
            Application label coming from request payload.

        Returns
        -------
        AppContext | None
            Matching context or ``None`` if the label is unknown.
        """
        return self._contexts_by_label.get(label)

    def write_exchange_buffer(self, app_context: AppContext, payload: bytes) -> None:
        """Write payload to the context exchange buffer.

        Parameters
        ----------
        app_context : AppContext
            Target context.
        payload : bytes
            Source bytes copied into the buffer and zero-padded.
        """
        app_context.exchange_buffer[:] = b"\x00" * EXCHANGE_BUFFER_LEN
        copy_len = min(len(payload), EXCHANGE_BUFFER_LEN)
        app_context.exchange_buffer[:copy_len] = payload[:copy_len]
        self.logger.debug(
            "exchange_to_kernel label=%d handle=%d bytes=%d",
            app_context.label,
            app_context.handle,
            copy_len,
        )

    def read_exchange_buffer(self, app_context: AppContext) -> bytes:
        """Read full exchange buffer for a context.

        Parameters
        ----------
        app_context : AppContext
            Source context.

        Returns
        -------
        bytes
            Full serialized exchange buffer.
        """
        payload = bytes(app_context.exchange_buffer)
        self.logger.debug(
            "exchange_from_kernel label=%d handle=%d bytes=%d",
            app_context.label,
            app_context.handle,
            len(payload),
        )
        return payload

    @property
    def bound_address(self) -> tuple[str, int]:
        """Return the effective bind address once server is started.

        Returns
        -------
        tuple[str, int]
            Bound host and port.

        Raises
        ------
        RuntimeError
            If server has not been started yet.
        """
        if self._bound_address is None:
            raise RuntimeError("daemon is not bound yet")
        return self._bound_address

    def serve_forever(
        self,
        stop_event: threading.Event | None = None,
        ready_event: threading.Event | None = None,
        poll_interval: float = 0.2,
    ) -> None:
        """Start the daemon and serve requests until stop is requested.

        Parameters
        ----------
        stop_event : threading.Event | None, optional
            External event used to request server shutdown.
        ready_event : threading.Event | None, optional
            Event set once binding and server startup are complete.
        poll_interval : float, optional
            Poll period in seconds when waiting for ``stop_event``.
        """
        event = stop_event if stop_event is not None else threading.Event()

        grpc_server = grpc.server(futures.ThreadPoolExecutor(max_workers=4))
        emulator_pb2_grpc.add_EmulatorServicer_to_server(
            _EmulatorServicer(daemon=self, store=self.store, logger=self.logger), grpc_server
        )  # type: ignore[no-untyped-call]

        bound_port = grpc_server.add_insecure_port(f"{self.host}:{self.port}")
        if bound_port == 0:
            self.logger.error("Cannot bind gRPC server on %s:%d", self.host, self.port)
            raise RuntimeError(f"cannot bind gRPC server on {self.host}:{self.port}")

        self._bound_address = (self.host, int(bound_port))
        grpc_server.start()

        self._startup_apps()

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
            self.logger.info("Sentry emulator stopped")


@dataclass(slots=True)
class _EmulatorServicer(emulator_pb2_grpc.EmulatorServicer):
    """Internal gRPC service implementation for syscall dispatch."""

    daemon: GrpcEmulatorDaemon
    store: SyscallStore
    logger: logging.Logger

    def Dispatch(
        self, request: Any, context: grpc.ServicerContext
    ) -> Any:
        """Handle one syscall dispatch gRPC request.

        Parameters
        ----------
        request : Any
            Incoming protobuf request payload.
        context : grpc.ServicerContext
            gRPC context used to return detailed error status.

        Returns
        -------
        Any
            ``DispatchResponse`` protobuf instance.
        """
        response_cls = getattr(emulator_pb2, "DispatchResponse")
        self.logger.debug(
            "Received request peer=%s syscall=%s args=%s label=%s payload_len=%d",
            context.peer(),
            getattr(request, "syscall", "<missing>"),
            list(getattr(request, "args", [])),
            getattr(request, "label", "<missing>"),
            len(getattr(request, "payload", b"")),
        )

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

        if message.syscall == "exchange_to_kernel":
            self.daemon.write_exchange_buffer(app_context, message.payload)
            self.logger.debug(
                "Responding syscall=%s label=%d status=0",
                message.syscall,
                message.label,
            )
            return response_cls(status=0, detail="ok")

        if message.syscall == "exchange_from_kernel":
            payload = self.daemon.read_exchange_buffer(app_context)
            self.logger.debug(
                "Responding syscall=%s label=%d status=0 payload_len=%d",
                message.syscall,
                message.label,
                len(payload),
            )
            return response_cls(
                status=0,
                detail="ok",
                payload=payload,
            )

        if message.syscall == "log":
            log_len = int(message.args[0]) if message.args else 0
            log_len = max(0, min(log_len, EXCHANGE_BUFFER_LEN))
            raw = bytes(app_context.exchange_buffer[:log_len])
            text = raw.split(b"\x00", 1)[0].decode("utf-8", errors="replace")
            print(text, flush=True)
            self.logger.debug(
                "Responding syscall=%s label=%d status=0 printed_len=%d",
                message.syscall,
                message.label,
                len(text),
            )
            return response_cls(status=0, detail="ok")

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
        self.logger.debug(
            "Responding syscall=%s label=%d status=0",
            message.syscall,
            message.label,
        )
        return response_cls(status=0, detail="ok")
