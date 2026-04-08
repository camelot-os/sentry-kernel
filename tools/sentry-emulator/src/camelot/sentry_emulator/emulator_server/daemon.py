# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Daemon lifecycle and app context management for the emulator."""

from concurrent import futures
from dataclasses import dataclass, field
import logging
import os
import random
import subprocess
import threading
import time

import grpc

from ..dispatcher import SyscallStore
from ..grpc import emulator_pb2_grpc
from .constants import (
    DEFAULT_HOST,
    DEFAULT_PORT,
    EVENT_MAGIC,
    EVENT_TYPE_IPC,
    EVENT_TYPE_SIGNAL,
    EXCHANGE_BUFFER_LEN,
    MAX_PENDING_SIGNALS,
    PRECISION_CYCLE,
    PRECISION_MICROSECONDS,
    PRECISION_MILLISECONDS,
    PRECISION_NANOSECONDS,
    SIGNAL_ALARM,
    STATUS_BUSY,
    STATUS_INTR,
    STATUS_OK,
    UINT32_MAX,
)
from .models import AlarmRegistration, AppContext, PendingIPC, StartSpec


@dataclass(slots=True)
class GrpcEmulatorDaemon:
    """Lifecycle manager for the emulator gRPC daemon."""

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
        """Report whether every configured startup context has exited.

        Returns
        -------
        bool
            ``True`` only when startup specs exist and no context remains active.
        """
        if not self.start_specs:
            return False
        with self._lock:
            return not self._contexts_by_label

    def deactivate_context(self, app_context: AppContext, exit_code: int) -> bool:
        """Deactivate an application context after an ``exit`` syscall.

        Parameters
        ----------
        app_context : AppContext
            Context to remove from active registries.
        exit_code : int
            Application exit code reported by userspace.

        Returns
        -------
        bool
            ``True`` when this deactivation leaves no startup contexts alive.
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
            pending_ipcs = list(app_context.pending_ipcs)
            app_context.pending_ipcs.clear()
            app_context.event_condition.notify_all()

        for pending_ipc in pending_ipcs:
            pending_ipc.completion_status = STATUS_INTR
            pending_ipc.done.set()

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
        """Allocate the next unique app handle.

        Returns
        -------
        int
            Unsigned 32-bit process handle.

        Raises
        ------
        RuntimeError
            If the handle space is exhausted.
        """
        if self._next_handle > UINT32_MAX:
            raise RuntimeError("app context handle overflow")
        handle = self._next_handle
        self._next_handle += 1
        return handle

    def _prepare_start_specs(self) -> None:
        """Validate startup specs and create contexts before process launch.

        Raises
        ------
        RuntimeError
            If labels collide or one executable path is missing.
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
        """Spawn all prepared startup applications.

        Raises
        ------
        RuntimeError
            If one prepared context is missing or process creation fails.
        """
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
        """Initialize contexts and launch configured startup apps."""
        if not self.start_specs:
            self.logger.info("No startup tasks configured")
            return

        self._prepare_start_specs()
        self._start_prepared_apps()

    def _terminate_started_apps(self) -> None:
        """Terminate started apps and clear all in-memory runtime contexts."""
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
                for pending_ipc in app_context.pending_ipcs:
                    pending_ipc.completion_status = STATUS_INTR
                    pending_ipc.done.set()
                app_context.pending_ipcs.clear()
                app_context.process = None
            self._contexts_by_label.clear()
            self._contexts_by_handle.clear()

    def context_for_label(self, label: int) -> AppContext | None:
        """Return the active context associated with one application label.

        Parameters
        ----------
        label : int
            Application label.

        Returns
        -------
        AppContext | None
            Matching active context or ``None`` when absent.
        """
        with self._lock:
            return self._contexts_by_label.get(label)

    def context_for_handle(self, handle: int) -> AppContext | None:
        """Return the active context associated with one process handle.

        Parameters
        ----------
        handle : int
            Process handle returned by ``get_process_handle``.

        Returns
        -------
        AppContext | None
            Matching active context or ``None`` when absent.
        """
        with self._lock:
            return self._contexts_by_handle.get(handle)

    def write_exchange_buffer(self, app_context: AppContext, payload: bytes) -> None:
        """Write bytes into one app exchange buffer with zero-padding.

        Parameters
        ----------
        app_context : AppContext
            Target app runtime context.
        payload : bytes
            Payload copied into the fixed-size exchange buffer.
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
        """Read one app exchange buffer as immutable bytes.

        Parameters
        ----------
        app_context : AppContext
            Source app runtime context.

        Returns
        -------
        bytes
            Snapshot of the full fixed-size exchange buffer.
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
        """Serialize and write one unsigned 32-bit integer to exchange buffer.

        Parameters
        ----------
        app_context : AppContext
            Target app runtime context.
        value : int
            Value encoded in little-endian unsigned representation.
        """
        self.write_exchange_buffer(app_context, int(value).to_bytes(4, "little", signed=False))

    def write_u64_to_exchange_buffer(self, app_context: AppContext, value: int) -> None:
        """Serialize and write one unsigned 64-bit integer to exchange buffer.

        Parameters
        ----------
        app_context : AppContext
            Target app runtime context.
        value : int
            Value encoded in little-endian unsigned representation.
        """
        self.write_exchange_buffer(app_context, int(value).to_bytes(8, "little", signed=False))

    def queue_signal(self, target: AppContext, signal: int, source_handle: int) -> int:
        """Queue a signal event for one application context.

        Parameters
        ----------
        target : AppContext
            Destination app context receiving the signal.
        signal : int
            Signal value to enqueue.
        source_handle : int
            Handle of the sender process.

        Returns
        -------
        int
            ``STATUS_OK`` on success, ``STATUS_BUSY`` when queue is full.
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

    def queue_ipc(self, target: AppContext, source_handle: int, payload: bytes) -> PendingIPC:
        """Queue an IPC event for one application context.

        Parameters
        ----------
        target : AppContext
            Destination app context receiving the IPC payload.
        source_handle : int
            Handle of the sender process.
        payload : bytes
            Sender payload copied from exchange memory.

        Returns
        -------
        PendingIPC
            In-flight IPC transfer token used by sender to wait for completion.
        """
        pending = PendingIPC(source_handle=source_handle, payload=bytes(payload))
        with target.event_condition:
            target.pending_ipcs.append(pending)
            target.event_condition.notify_all()
        self.logger.debug(
            "Queued IPC source=%d for label=%d handle=%d payload_len=%d",
            source_handle,
            target.label,
            target.handle,
            len(payload),
        )
        return pending

    @staticmethod
    def complete_ipc(pending_ipc: PendingIPC, status: int = STATUS_OK) -> None:
        """Resolve a pending IPC transfer with final sender status."""
        pending_ipc.completion_status = status
        pending_ipc.done.set()

    def _alarm_fire(self, label: int, delay_ms: int) -> None:
        """Deliver one alarm tick to the context identified by label.

        Parameters
        ----------
        label : int
            Target application label.
        delay_ms : int
            Alarm delay key used for logging context.
        """
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
        """Schedule a one-shot or periodic alarm for one context.

        Parameters
        ----------
        app_context : AppContext
            Target app runtime context.
        delay_ms : int
            Alarm delay in milliseconds.
        periodic : bool
            Whether the alarm should re-arm itself after firing.

        Returns
        -------
        int
            ``STATUS_OK`` when scheduled, ``STATUS_BUSY`` on duplicate delay.
        """
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
        app_context.alarms[delay_ms] = AlarmRegistration(
            delay_ms=delay_ms,
            periodic=periodic,
            timer=timer,
        )
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
        """Stop one previously scheduled alarm.

        Parameters
        ----------
        app_context : AppContext
            Target app runtime context.
        delay_ms : int
            Alarm delay key identifying the registration.

        Returns
        -------
        int
            ``STATUS_OK`` regardless of prior registration presence.
        """
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
        """Return monotonic elapsed time encoded for requested precision.

        Parameters
        ----------
        precision : int
            Precision code from ``PRECISION_*`` constants.

        Returns
        -------
        int
            Elapsed monotonic time converted to the requested unit.

        Raises
        ------
        ValueError
            If precision is not supported by the emulator API.
        """
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

    def _has_matching_signal(self, app_context: AppContext, mask: int) -> bool:
        """Return whether one matching signal is immediately available."""
        return bool(mask & EVENT_TYPE_SIGNAL) and bool(app_context.pending_signals)

    def _has_matching_ipc(self, app_context: AppContext, mask: int) -> bool:
        """Return whether one matching IPC event is immediately available."""
        return bool(mask & EVENT_TYPE_IPC) and bool(app_context.pending_ipcs)

    def _dequeue_matching_signal(
        self, app_context: AppContext, mask: int
    ) -> tuple[int, int] | None:
        """Pop one pending signal if the provided mask accepts signal events.

        Parameters
        ----------
        app_context : AppContext
            Source app runtime context.
        mask : int
            Bitmask of accepted event types.

        Returns
        -------
        tuple[int, int] | None
            ``(signal, source_handle)`` when available, otherwise ``None``.
        """
        if not (mask & EVENT_TYPE_SIGNAL):
            return None

        with app_context.event_condition:
            if not app_context.pending_signals:
                return None
            return app_context.pending_signals.pop(0)

    def _dequeue_matching_ipc(self, app_context: AppContext, mask: int) -> PendingIPC | None:
        """Pop one pending IPC if the provided mask accepts IPC events."""
        if not (mask & EVENT_TYPE_IPC):
            return None

        with app_context.event_condition:
            if not app_context.pending_ipcs:
                return None
            return app_context.pending_ipcs.pop(0)

    def _serialize_signal_event(
        self, app_context: AppContext, signal: int, source_handle: int
    ) -> None:
        """Serialize one signal event into the app exchange buffer.

        Parameters
        ----------
        app_context : AppContext
            Target app runtime context.
        signal : int
            Signal value to encode in payload.
        source_handle : int
            Handle of the sender process.
        """
        header = bytes([EVENT_TYPE_SIGNAL, 4]) + EVENT_MAGIC.to_bytes(
            2, "little"
        ) + int(source_handle).to_bytes(4, "little", signed=False)
        payload = int(signal).to_bytes(4, "little", signed=False)
        self.write_exchange_buffer(app_context, header + payload)

    def _serialize_ipc_event(
        self, app_context: AppContext, payload: bytes, source_handle: int
    ) -> None:
        """Serialize one IPC event into the app exchange buffer."""
        header = bytes([EVENT_TYPE_IPC, len(payload)]) + EVENT_MAGIC.to_bytes(
            2, "little"
        ) + int(source_handle).to_bytes(4, "little", signed=False)
        self.write_exchange_buffer(app_context, header + payload)

    @property
    def bound_address(self) -> tuple[str, int]:
        """Return bound host and port for the running gRPC server.

        Returns
        -------
        tuple[str, int]
            Bound ``(host, port)`` pair.

        Raises
        ------
        RuntimeError
            If server binding has not happened yet.
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
        """Run the gRPC server loop until stop criteria are met.

        Parameters
        ----------
        stop_event : threading.Event | None, optional
            External stop signal, by default a fresh event local to this call.
        ready_event : threading.Event | None, optional
            Event set once the server is bound and started.
        poll_interval : float, optional
            Delay in seconds between stop-condition polls.

        Raises
        ------
        RuntimeError
            If gRPC binding fails or startup app preparation fails.
        """
        event = stop_event if stop_event is not None else threading.Event()

        grpc_server = grpc.server(futures.ThreadPoolExecutor(max_workers=4))
        from .servicer import EmulatorServicer

        emulator_pb2_grpc.add_EmulatorServicer_to_server(
            EmulatorServicer(daemon=self, store=self.store, logger=self.logger), grpc_server
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
