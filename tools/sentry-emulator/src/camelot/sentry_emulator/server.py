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
import random
import subprocess
import threading
import time
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
SIGNAL_ABORT: Final[int] = 1
EVENT_TYPE_SIGNAL: Final[int] = 2
SIGNAL_USR2: Final[int] = 12
SIGNAL_ALARM: Final[int] = 2
EVENT_MAGIC: Final[int] = 0x4242
PRECISION_CYCLE: Final[int] = 0
PRECISION_NANOSECONDS: Final[int] = 1
PRECISION_MICROSECONDS: Final[int] = 2
PRECISION_MILLISECONDS: Final[int] = 3

STATUS_OK: Final[int] = 0
STATUS_INVALID: Final[int] = 1
STATUS_DENIED: Final[int] = 2
STATUS_NO_ENTITY: Final[int] = 3
STATUS_BUSY: Final[int] = 4
STATUS_TIMEOUT: Final[int] = 7
STATUS_AGAIN: Final[int] = 8

MAX_PENDING_SIGNALS: Final[int] = 32


@dataclass(slots=True)
class AlarmRegistration:
    delay_ms: int
    periodic: bool
    timer: threading.Timer


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


@dataclass(slots=True)
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
    process : subprocess.Popen[bytes] | None
        Spawned process object for lifecycle management.
    exchange_buffer : bytearray
        Per-application exchange zone content.
    pending_signals : list[tuple[int, int]]
        Pending signals queued as ``(signal, source_handle)`` tuples.
    alarms : dict[int, AlarmRegistration]
        Alarm registrations keyed by timeout in milliseconds.
    event_condition : threading.Condition
        Condition used to block ``wait_for_event`` until an event is available.
    """

    label: int
    handle: int
    app_path: Path
    process: subprocess.Popen[bytes] | None = None
    exchange_buffer: bytearray = field(
        default_factory=lambda: bytearray(EXCHANGE_BUFFER_LEN)
    )
    pending_signals: list[tuple[int, int]] = field(default_factory=list)
    alarms: dict[int, AlarmRegistration] = field(default_factory=dict)
    event_condition: threading.Condition = field(default_factory=threading.Condition)
    exit_code: int | None = None


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
    _contexts_by_handle: dict[int, AppContext] = field(default_factory=dict, init=False)
    _started_processes: list[subprocess.Popen[bytes]] = field(default_factory=list, init=False)
    _next_handle: int = field(default=1, init=False)
    _rng: random.Random = field(default_factory=random.Random, init=False)
    _lock: threading.Lock = field(default_factory=threading.Lock, init=False)
    _start_monotonic_ns: int = field(default_factory=time.monotonic_ns, init=False)

    def _all_startup_contexts_stopped(self) -> bool:
        """Return ``True`` when all startup contexts have been deactivated."""
        if not self.start_specs:
            return False
        with self._lock:
            return not self._contexts_by_label

    def deactivate_context(self, app_context: AppContext, exit_code: int) -> bool:
        """Deactivate one application context after an ``exit`` syscall.

        Parameters
        ----------
        app_context : AppContext
            Context to deactivate.
        exit_code : int
            Application-provided process return code.

        Returns
        -------
        bool
            ``True`` when this deactivation makes all startup contexts inactive.
        """
        with self._lock:
            removed_by_label = self._contexts_by_label.pop(app_context.label, None)
            removed_by_handle = self._contexts_by_handle.pop(app_context.handle, None)
            contexts_remaining = len(self._contexts_by_label)

        if removed_by_label is None or removed_by_handle is None:
            return self._all_startup_contexts_stopped()

        app_context.exit_code = exit_code
        with app_context.event_condition:
            app_context.pending_signals.clear()
            app_context.event_condition.notify_all()

        for registration in app_context.alarms.values():
            registration.timer.cancel()
        app_context.alarms.clear()

        self.logger.info(
            "App exited label=%d handle=%d code=%d remaining_contexts=%d",
            app_context.label,
            app_context.handle,
            exit_code,
            contexts_remaining,
        )
        return contexts_remaining == 0 and bool(self.start_specs)

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

    def _prepare_start_specs(self) -> None:
        """Create and register all startup contexts before launching apps.

        Parameters
        ----------
        Raises
        ------
        RuntimeError
            If labels are duplicated or one executable path is invalid.
        """
        prepared_contexts: list[AppContext] = []
        labels: set[int] = set()
        for spec in self.start_specs:
            if spec.label in labels or spec.label in self._contexts_by_label:
                self.logger.error("Duplicate startup label detected: %d", spec.label)
                raise RuntimeError(f"duplicate app label: {spec.label}")

            app_path = spec.app_path.expanduser().resolve()
            if not app_path.exists():
                self.logger.error("Startup executable does not exist: %s", app_path)
                raise RuntimeError(f"app does not exist: {app_path}")

            prepared_contexts.append(
                AppContext(
                    label=spec.label,
                    handle=self._allocate_handle(),
                    app_path=app_path,
                )
            )
            labels.add(spec.label)

        with self._lock:
            for context in prepared_contexts:
                self._contexts_by_label[context.label] = context
                self._contexts_by_handle[context.handle] = context

        for context in prepared_contexts:
            self.logger.debug(
                "Initialized app context label=%d handle=%d path=%s",
                context.label,
                context.handle,
                context.app_path,
            )

    def _start_prepared_apps(self) -> None:
        """Start all applications after contexts have been registered."""
        for spec in self.start_specs:
            with self._lock:
                context = self._contexts_by_label.get(spec.label)

            if context is None:
                self.logger.error("Missing initialized context for label=%d", spec.label)
                raise RuntimeError(f"missing app context for label: {spec.label}")

            child_env = os.environ.copy()
            child_env["SENTRY_APP_LABEL"] = str(spec.label)
            child_env["SENTRY_EMULATOR_HOST"] = self.host
            child_env["SENTRY_EMULATOR_PORT"] = str(self.port)

            try:
                process = subprocess.Popen([str(context.app_path)], env=child_env)
            except OSError as exc:
                self.logger.error(
                    "Cannot start app label=%d path=%s: %s",
                    spec.label,
                    context.app_path,
                    exc,
                )
                raise RuntimeError(f"cannot start app: {context.app_path}") from exc

            context.process = process
            with self._lock:
                self._started_processes.append(process)

            self.logger.info(
                "Started app label=%d handle=%d pid=%d path=%s",
                context.label,
                context.handle,
                process.pid,
                context.app_path,
            )

    def _startup_apps(self) -> None:
        """Start and register all configured startup applications."""
        if not self.start_specs:
            self.logger.info("No startup tasks configured")
            return

        self._prepare_start_specs()
        self._start_prepared_apps()

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

        with self._lock:
            for app_context in self._contexts_by_label.values():
                for registration in app_context.alarms.values():
                    registration.timer.cancel()
                app_context.alarms.clear()
                app_context.pending_signals.clear()
                app_context.process = None
            self._contexts_by_label.clear()
            self._contexts_by_handle.clear()

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
        with self._lock:
            return self._contexts_by_label.get(label)

    def context_for_handle(self, handle: int) -> AppContext | None:
        """Look up the runtime context bound to a handle."""
        with self._lock:
            return self._contexts_by_handle.get(handle)

    def write_exchange_buffer(self, app_context: AppContext, payload: bytes) -> None:
        """Write payload to the context exchange buffer.

        Parameters
        ----------
        app_context : AppContext
            Target context.
        payload : bytes
            Source bytes copied into the buffer and zero-padded.
        """
        with self._lock:
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
        with self._lock:
            payload = bytes(app_context.exchange_buffer)
        self.logger.debug(
            "exchange_from_kernel label=%d handle=%d bytes=%d",
            app_context.label,
            app_context.handle,
            len(payload),
        )
        return payload

    def write_u32_to_exchange_buffer(self, app_context: AppContext, value: int) -> None:
        """Store one ``u32`` value into app exchange buffer."""
        self.write_exchange_buffer(app_context, int(value).to_bytes(4, "little", signed=False))

    def write_u64_to_exchange_buffer(self, app_context: AppContext, value: int) -> None:
        """Store one ``u64`` value into app exchange buffer."""
        self.write_exchange_buffer(app_context, int(value).to_bytes(8, "little", signed=False))

    def queue_signal(self, target: AppContext, signal: int, source_handle: int) -> int:
        """Queue a signal for a target context.

        Returns
        -------
        int
            Emulator status code.
        """
        with target.event_condition:
            if len(target.pending_signals) >= MAX_PENDING_SIGNALS:
                return STATUS_BUSY
            target.pending_signals.append((signal, source_handle))
            target.event_condition.notify_all()
        self.logger.debug(
            "Queued signal=%d source=%d for label=%d handle=%d",
            signal,
            source_handle,
            target.label,
            target.handle,
        )
        return STATUS_OK

    def _alarm_fire(self, label: int, delay_ms: int) -> None:
        with self._lock:
            target = self._contexts_by_label.get(label)
        if target is None:
            return
        status = self.queue_signal(target, SIGNAL_ALARM, target.handle)
        if status != STATUS_OK:
            self.logger.warning(
                "Alarm delivery failed label=%d delay_ms=%d status=%d",
                label,
                delay_ms,
                status,
            )

    def _schedule_alarm(self, app_context: AppContext, delay_ms: int, periodic: bool) -> int:
        with self._lock:
            if delay_ms in app_context.alarms:
                return STATUS_BUSY

        interval_s = max(0.0, delay_ms / 1000.0)

        def _callback() -> None:
            self._alarm_fire(app_context.label, delay_ms)
            if not periodic:
                with self._lock:
                    app_context.alarms.pop(delay_ms, None)
                return

            with self._lock:
                still_registered = app_context.alarms.get(delay_ms)
                if still_registered is None:
                    return

                next_timer = threading.Timer(interval_s, _callback)
                app_context.alarms[delay_ms] = AlarmRegistration(
                    delay_ms=delay_ms,
                    periodic=True,
                    timer=next_timer,
                )
            next_timer.start()

        timer = threading.Timer(interval_s, _callback)
        registration = AlarmRegistration(delay_ms=delay_ms, periodic=periodic, timer=timer)
        with self._lock:
            app_context.alarms[delay_ms] = registration
        timer.start()
        self.logger.debug(
            "Scheduled alarm label=%d handle=%d delay_ms=%d periodic=%s",
            app_context.label,
            app_context.handle,
            delay_ms,
            periodic,
        )
        return STATUS_OK

    def _stop_alarm(self, app_context: AppContext, delay_ms: int) -> int:
        with self._lock:
            registration = app_context.alarms.pop(delay_ms, None)
        if registration is None:
            self.logger.debug(
                "Alarm already stopped label=%d handle=%d delay_ms=%d",
                app_context.label,
                app_context.handle,
                delay_ms,
            )
            return STATUS_OK
        registration.timer.cancel()
        self.logger.debug(
            "Stopped alarm label=%d handle=%d delay_ms=%d",
            app_context.label,
            app_context.handle,
            delay_ms,
        )
        return STATUS_OK

    def current_cycle_value(self, precision: int) -> int:
        """Compute a synthetic cycle/timestamp value for requested precision."""
        elapsed_ns = max(0, time.monotonic_ns() - self._start_monotonic_ns)
        if precision == PRECISION_CYCLE:
            return elapsed_ns
        if precision == PRECISION_NANOSECONDS:
            return elapsed_ns
        if precision == PRECISION_MICROSECONDS:
            return elapsed_ns // 1_000
        if precision == PRECISION_MILLISECONDS:
            return elapsed_ns // 1_000_000
        raise ValueError("invalid precision")

    def _dequeue_matching_signal(
        self, app_context: AppContext, mask: int
    ) -> tuple[int, int] | None:
        if not (mask & EVENT_TYPE_SIGNAL):
            return None

        with app_context.event_condition:
            if not app_context.pending_signals:
                return None
            return app_context.pending_signals.pop(0)

    def _serialize_signal_event(
        self, app_context: AppContext, signal: int, source_handle: int
    ) -> None:
        header = bytes(
            [EVENT_TYPE_SIGNAL, 4]
        ) + EVENT_MAGIC.to_bytes(2, "little") + int(source_handle).to_bytes(
            4, "little", signed=False
        )
        payload = int(signal).to_bytes(4, "little", signed=False)
        self.write_exchange_buffer(app_context, header + payload)

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
            while True:
                if event.wait(timeout=poll_interval):
                    break
                if self._all_startup_contexts_stopped():
                    self.logger.info(
                        "All startup tasks have terminated, stopping emulator daemon"
                    )
                    break
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
            print(f"[app:{message.label}] {text}", flush=True)
            self.logger.debug(
                "Responding syscall=%s label=%d status=0 printed_len=%d",
                message.syscall,
                message.label,
                len(text),
            )
            return response_cls(status=0, detail="ok")

        if message.syscall == "get_process_handle":
            if not message.args:
                detail = "missing label argument"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            target_label = int(message.args[0])
            target_context = self.daemon.context_for_label(target_label)
            if target_context is None:
                return response_cls(status=STATUS_INVALID, detail="unknown label")

            self.daemon.write_u32_to_exchange_buffer(app_context, target_context.handle)
            return response_cls(status=STATUS_OK, detail="ok")

        if message.syscall == "send_signal":
            if len(message.args) < 2:
                detail = "missing send_signal arguments"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            target_handle = int(message.args[0])
            signal = int(message.args[1])
            if target_handle == app_context.handle:
                return response_cls(status=STATUS_INVALID, detail="self signal forbidden")
            if signal < SIGNAL_ABORT or signal > SIGNAL_USR2:
                return response_cls(status=STATUS_INVALID, detail="invalid signal")

            target_context = self.daemon.context_for_handle(target_handle)
            if target_context is None:
                return response_cls(status=STATUS_INVALID, detail="unknown target handle")

            status = self.daemon.queue_signal(target_context, signal, app_context.handle)
            return response_cls(status=status, detail="ok" if status == STATUS_OK else "busy")

        if message.syscall == "wait_for_event":
            if len(message.args) < 2:
                detail = "missing wait_for_event arguments"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            mask = int(message.args[0])
            timeout = int(message.args[1])

            pending = self.daemon._dequeue_matching_signal(app_context, mask)
            if pending is not None:
                signal, source_handle = pending
                self.daemon._serialize_signal_event(app_context, signal, source_handle)
                return response_cls(status=STATUS_OK, detail="ok")

            if timeout == -1:
                return response_cls(status=STATUS_AGAIN, detail="again")

            wait_timeout = None if timeout == 0 else max(0.0, timeout / 1000.0)
            with app_context.event_condition:
                has_event = app_context.event_condition.wait_for(
                    lambda: bool(app_context.pending_signals) and bool(mask & EVENT_TYPE_SIGNAL),
                    timeout=wait_timeout,
                )
                if not has_event:
                    return response_cls(status=STATUS_TIMEOUT, detail="timeout")
                signal, source_handle = app_context.pending_signals.pop(0)

            self.daemon._serialize_signal_event(app_context, signal, source_handle)
            return response_cls(status=STATUS_OK, detail="ok")

        if message.syscall == "alarm":
            if len(message.args) < 2:
                detail = "missing alarm arguments"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            delay_ms = max(0, int(message.args[0]))
            flag = int(message.args[1])
            if flag == 0:
                status = self.daemon._schedule_alarm(app_context, delay_ms, periodic=False)
                return response_cls(status=status, detail="ok" if status == STATUS_OK else "busy")
            if flag == 1:
                status = self.daemon._schedule_alarm(app_context, delay_ms, periodic=True)
                return response_cls(status=status, detail="ok" if status == STATUS_OK else "busy")
            if flag == 2:
                status = self.daemon._stop_alarm(app_context, delay_ms)
                return response_cls(
                    status=status,
                    detail="ok" if status == STATUS_OK else "no entity",
                )
            return response_cls(status=STATUS_INVALID, detail="invalid alarm flag")

        if message.syscall == "get_random":
            value = self.daemon._rng.getrandbits(32)
            self.daemon.write_u32_to_exchange_buffer(app_context, value)
            return response_cls(status=STATUS_OK, detail="ok")

        if message.syscall == "get_cycle":
            if not message.args:
                detail = "missing precision argument"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            precision = int(message.args[0])
            if precision < PRECISION_CYCLE or precision > PRECISION_MILLISECONDS:
                return response_cls(status=STATUS_INVALID, detail="invalid precision")

            cycle_value = self.daemon.current_cycle_value(precision)
            self.daemon.write_u64_to_exchange_buffer(app_context, cycle_value)
            return response_cls(status=STATUS_OK, detail="ok")

        if message.syscall == "exit":
            exit_code = int(message.args[0]) if message.args else 0
            all_done = self.daemon.deactivate_context(app_context, exit_code)
            detail = "all tasks exited" if all_done else "context deactivated"
            return response_cls(status=STATUS_OK, detail=detail)

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
