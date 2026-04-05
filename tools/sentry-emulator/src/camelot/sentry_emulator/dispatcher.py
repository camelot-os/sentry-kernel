# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""In-memory syscall dispatch bookkeeping.

The daemon currently stores accepted syscall messages in memory for inspection
and tests. This module centralizes that behavior.
"""

from collections import defaultdict
from dataclasses import dataclass, field

from .protocol import SyscallMessage


@dataclass(slots=True)
class SyscallStore:
    """Store incoming syscall messages grouped by syscall name.

    Attributes
    ----------
    buckets : dict[str, list[SyscallMessage]]
        Mapping from syscall name to all corresponding messages.
    invalid_packets : int
        Number of rejected requests due to protocol or routing errors.
    """

    buckets: dict[str, list[SyscallMessage]] = field(
        default_factory=lambda: defaultdict(list)
    )
    invalid_packets: int = 0

    def register(self, message: SyscallMessage) -> None:
        """Register a valid syscall message.

        Parameters
        ----------
        message : SyscallMessage
            Validated syscall payload to store.
        """
        self.buckets[message.syscall].append(message)

    def register_invalid(self) -> None:
        """Increment the invalid packet counter."""
        self.invalid_packets += 1

    def count_for(self, syscall_name: str) -> int:
        """Return the number of stored calls for one syscall name.

        Parameters
        ----------
        syscall_name : str
            Syscall name key in the store.

        Returns
        -------
        int
            Number of registered messages for ``syscall_name``.
        """
        return len(self.buckets.get(syscall_name, []))

    def snapshot_counts(self) -> dict[str, int]:
        """Return a compact count snapshot for all known syscalls.

        Returns
        -------
        dict[str, int]
            Mapping from syscall names to message counts.
        """
        return {name: len(entries) for name, entries in self.buckets.items()}
