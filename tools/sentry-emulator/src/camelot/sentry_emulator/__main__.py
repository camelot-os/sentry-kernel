# SPDX-FileCopyrightText: 2026 H2Lab Development Team
# SPDX-License-Identifier: Apache-2.0

"""Module entrypoint for ``python -m camelot.sentry_emulator``."""

from .cli import main

if __name__ == "__main__":
    raise SystemExit(main())
