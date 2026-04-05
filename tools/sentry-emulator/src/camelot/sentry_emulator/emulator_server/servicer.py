# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""gRPC dispatch servicer for the emulator daemon."""

from dataclasses import dataclass
import logging
from typing import Any

import grpc

from ..dispatcher import SyscallStore
from ..grpc import emulator_pb2, emulator_pb2_grpc
from ..protocol import ProtocolError, deserialize_request
from .constants import (
    EXCHANGE_BUFFER_LEN,
    EVENT_TYPE_SIGNAL,
    PRECISION_CYCLE,
    PRECISION_MILLISECONDS,
    SIGNAL_ABORT,
    SIGNAL_USR2,
    STATUS_AGAIN,
    STATUS_INVALID,
    STATUS_OK,
    STATUS_TIMEOUT,
)


@dataclass(slots=True)
class EmulatorServicer(emulator_pb2_grpc.EmulatorServicer):
    """Internal gRPC service implementation for syscall dispatch."""

    daemon: Any
    store: SyscallStore
    logger: logging.Logger

    def Dispatch(self, request: Any, context: grpc.ServicerContext) -> Any:
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
