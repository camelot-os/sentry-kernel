# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0


from __future__ import annotations

import argparse
import logging

from .server import (
    DEFAULT_HOST,
    DEFAULT_PORT,
    GrpcEmulatorDaemon,
    StartSpec,
    parse_start_option,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="sentry-emulator",
        description="Run the Camelot Sentry userspace emulator daemon.",
    )
    parser.add_argument(
        "--host",
        default=DEFAULT_HOST,
        help=f"gRPC listening interface (default: {DEFAULT_HOST})",
    )
    parser.add_argument(
        "--port",
        default=DEFAULT_PORT,
        type=int,
        help=f"gRPC listening port (default: {DEFAULT_PORT})",
    )
    parser.add_argument(
        "--log-level",
        default="INFO",
        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
        help="Daemon log level",
    )
    parser.add_argument(
        "--start",
        action="append",
        default=[],
        metavar="APP,label=<u32>",
        help="Start an application and register context for this label (repeatable)",
    )
    return parser


def _parse_start_specs(raw_specs: list[str], parser: argparse.ArgumentParser) -> tuple[StartSpec, ...]:
    parsed: list[StartSpec] = []
    for raw in raw_specs:
        try:
            parsed.append(parse_start_option(raw))
        except ValueError as exc:
            parser.error(str(exc))
    return tuple(parsed)


def main() -> int:
    parser = _build_parser()
    args = parser.parse_args()
    start_specs = _parse_start_specs(args.start, parser)

    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )

    daemon = GrpcEmulatorDaemon(host=args.host, port=args.port, start_specs=start_specs)
    try:
        daemon.serve_forever()
    except KeyboardInterrupt:
        logging.getLogger("camelot.sentry_emulator").info("Shutdown requested")

    return 0
