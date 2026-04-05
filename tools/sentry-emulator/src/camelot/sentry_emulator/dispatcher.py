# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field

from .protocol import SyscallMessage


@dataclass(slots=True)
class SyscallStore:
    """In-memory store that groups incoming syscalls by syscall name."""

    buckets: dict[str, list[SyscallMessage]] = field(
        default_factory=lambda: defaultdict(list)
    )
    invalid_packets: int = 0

    def register(self, message: SyscallMessage) -> None:
        self.buckets[message.syscall].append(message)

    def register_invalid(self) -> None:
        self.invalid_packets += 1

    def count_for(self, syscall_name: str) -> int:
        return len(self.buckets.get(syscall_name, []))

    def snapshot_counts(self) -> dict[str, int]:
        return {name: len(entries) for name, entries in self.buckets.items()}
