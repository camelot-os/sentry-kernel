# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Command-line interface for the Sentry emulator daemon.

This module defines the public executable behavior used by the
``sentry-emulator`` console script. It validates CLI arguments, configures
logging, builds startup application specifications, and starts the gRPC daemon.
"""

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
    """Create the command-line parser for the emulator daemon.

    Returns
    -------
    argparse.ArgumentParser
        Parser configured with network, logging, and startup options.
    """
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
        help=(
            "Daemon verbosity: INFO=start/stop lifecycle, "
            "WARNING=invalid request content, ERROR=invalid args/start failures, "
            "DEBUG=full request/response and task events"
        ),
    )
    parser.add_argument(
        "--start",
        action="append",
        default=[],
        metavar="APP,label=<u32>",
        help="Start an application and register context for this label (repeatable)",
    )
    return parser


def _parse_start_specs(raw_specs: list[str]) -> tuple[StartSpec, ...]:
    """Parse and validate ``--start`` values into startup specifications.

    Parameters
    ----------
    raw_specs : list[str]
        Raw values provided by repeated ``--start`` arguments.
    Returns
    -------
    tuple[StartSpec, ...]
        Validated startup specifications in input order.

    Raises
    ------
    ValueError
        If any ``--start`` entry has invalid syntax or values.
    """
    parsed: list[StartSpec] = []
    for raw in raw_specs:
        parsed.append(parse_start_option(raw))
    return tuple(parsed)


def main() -> int:
    """Run the daemon CLI entrypoint.

    Returns
    -------
    int
        Process return code (``0`` for graceful termination).
    """
    parser = _build_parser()
    args = parser.parse_args()

    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    logger = logging.getLogger("camelot.sentry_emulator")

    if args.port < 0 or args.port > 65535:
        logger.error("Invalid --port value: %d (expected in [0, 65535])", args.port)
        return 2

    try:
        start_specs = _parse_start_specs(args.start)
    except ValueError as exc:
        logger.error("Invalid startup argument: %s", exc)
        return 2

    daemon = GrpcEmulatorDaemon(host=args.host, port=args.port, start_specs=start_specs)
    try:
        daemon.serve_forever()
    except KeyboardInterrupt:
        logger.info("Shutdown requested")
    except RuntimeError as exc:
        logger.error("Daemon startup failed: %s", exc)
        return 1

    return 0
