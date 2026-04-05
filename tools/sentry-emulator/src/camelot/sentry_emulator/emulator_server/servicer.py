# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""gRPC dispatch servicer for the emulator daemon."""

from dataclasses import dataclass
import logging
import time
from typing import Any

import grpc

from ..dispatcher import SyscallStore
from ..grpc import emulator_pb2, emulator_pb2_grpc
from ..protocol import ProtocolError, deserialize_request
from .constants import (
    EXCHANGE_BUFFER_LEN,
    PRECISION_CYCLE,
    PRECISION_MILLISECONDS,
    SIGNAL_ABORT,
    SIGNAL_USR2,
    STATUS_AGAIN,
    STATUS_INTR,
    STATUS_INVALID,
    STATUS_OK,
    STATUS_TIMEOUT,
)

IPC_EVENT_HEADER_LEN = 8
MAX_IPC_PAYLOAD_LEN = EXCHANGE_BUFFER_LEN - IPC_EVENT_HEADER_LEN


@dataclass(slots=True)
class EmulatorServicer(emulator_pb2_grpc.EmulatorServicer):
    """Internal gRPC service implementation for syscall dispatch.

    Attributes
    ----------
    daemon : Any
        Runtime daemon object handling app contexts and buffer operations.
    store : SyscallStore
        In-memory syscall bookkeeping used by tests and diagnostics.
    logger : logging.Logger
        Logger used for request-level tracing and warnings.
    """

    daemon: Any
    store: SyscallStore
    logger: logging.Logger

    def Dispatch(self, request: Any, context: grpc.ServicerContext) -> Any:
        """Handle one emulator syscall request.

        Parameters
        ----------
        request : Any
            gRPC ``DispatchRequest`` protobuf payload.
        context : grpc.ServicerContext
            gRPC request context used for peer metadata and status reporting.

        Returns
        -------
        Any
            ``DispatchResponse`` protobuf message carrying status, detail, and
            optional payload.
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
            return response_cls(status=0, detail="ok", payload=payload)

        if message.syscall == "log":
            log_len = int(message.args[0]) if message.args else 0
            log_len = max(0, min(log_len, EXCHANGE_BUFFER_LEN))
            raw = bytes(app_context.exchange_buffer[:log_len])
            text = raw.split(b"\x00", 1)[0].decode("utf-8", errors="replace")
            print(f"[{app_context.app_name}:{message.label}] {text}", flush=True)
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

        if message.syscall == "send_ipc":
            if len(message.args) < 2:
                detail = "missing send_ipc arguments"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            target_handle = int(message.args[0])
            ipc_len = int(message.args[1])
            if target_handle == app_context.handle:
                return response_cls(status=STATUS_INVALID, detail="self ipc forbidden")
            if ipc_len < 0 or ipc_len > MAX_IPC_PAYLOAD_LEN:
                return response_cls(status=STATUS_INVALID, detail="invalid ipc length")

            target_context = self.daemon.context_for_handle(target_handle)
            if target_context is None:
                return response_cls(status=STATUS_INVALID, detail="unknown target handle")

            payload = self.daemon.read_exchange_buffer(app_context)[:ipc_len]
            pending_ipc = self.daemon.queue_ipc(target_context, app_context.handle, payload)
            pending_ipc.done.wait()

            final_status = pending_ipc.completion_status
            if final_status is None:
                final_status = STATUS_INTR
            return response_cls(
                status=final_status,
                detail="ok" if final_status == STATUS_OK else "interrupted",
            )

        if message.syscall == "wait_for_event":
            if len(message.args) < 2:
                detail = "missing wait_for_event arguments"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            mask = int(message.args[0])
            timeout = int(message.args[1])

            pending_signal = self.daemon._dequeue_matching_signal(app_context, mask)
            if pending_signal is not None:
                signal, source_handle = pending_signal
                self.daemon._serialize_signal_event(app_context, signal, source_handle)
                return response_cls(status=STATUS_OK, detail="ok")

            pending_ipc = self.daemon._dequeue_matching_ipc(app_context, mask)
            if pending_ipc is not None:
                self.daemon._serialize_ipc_event(
                    app_context,
                    pending_ipc.payload,
                    pending_ipc.source_handle,
                )
                self.daemon.complete_ipc(pending_ipc)
                return response_cls(status=STATUS_OK, detail="ok")

            if timeout == -1:
                return response_cls(status=STATUS_AGAIN, detail="again")

            wait_timeout = None if timeout == 0 else max(0.0, timeout / 1000.0)
            with app_context.event_condition:
                has_event = app_context.event_condition.wait_for(
                    lambda: self.daemon._has_matching_signal(app_context, mask)
                    or self.daemon._has_matching_ipc(app_context, mask),
                    timeout=wait_timeout,
                )
                if not has_event:
                    return response_cls(status=STATUS_TIMEOUT, detail="timeout")

                signal: int | None = None
                source_handle: int | None = None
                pending_ipc = None
                if self.daemon._has_matching_signal(app_context, mask):
                    signal, source_handle = app_context.pending_signals.pop(0)
                elif self.daemon._has_matching_ipc(app_context, mask):
                    pending_ipc = app_context.pending_ipcs.pop(0)

            if signal is not None and source_handle is not None:
                self.daemon._serialize_signal_event(app_context, signal, source_handle)
                return response_cls(status=STATUS_OK, detail="ok")
            if pending_ipc is not None:
                self.daemon._serialize_ipc_event(
                    app_context,
                    pending_ipc.payload,
                    pending_ipc.source_handle,
                )
                self.daemon.complete_ipc(pending_ipc)
                return response_cls(status=STATUS_OK, detail="ok")
            return response_cls(status=STATUS_TIMEOUT, detail="timeout")

        if message.syscall == "sleep":
            if len(message.args) < 2:
                detail = "missing sleep arguments"
                self.logger.warning("Rejected command from %s: %s", context.peer(), detail)
                context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
                context.set_details(detail)
                return response_cls(status=STATUS_INVALID, detail=detail)

            duration_ms = int(message.args[0])
            if duration_ms < 0:
                return response_cls(status=STATUS_INVALID, detail="invalid sleep duration")

            # In emulator mode, sleep completion is controlled by daemon-side timing.
            # The RPC returns only when the requested duration has elapsed.
            time.sleep(duration_ms / 1000.0)
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
