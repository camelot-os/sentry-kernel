<!-- SPDX-FileCopyrightText: 2026 H2Lab Development Team -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Camelot Sentry Emulator

This package provides a gRPC daemon used by the POSIX implementation of the `sentry-uapi` crate.

## Features

- listens on gRPC (`127.0.0.1:44044` by default)
- receives syscall commands emitted by the POSIX Rust backend
- protobuf-based serialization/deserialization for syscall payloads
- traces each deserialized command to daemon stderr logs
- validates incoming commands and sorts them by syscall name
- starts applications with labeled contexts (`--start app.elf,label=<u32>`)
- assigns one unique context handle per started application

## Run

```sh
sentry-emulator --host 127.0.0.1 --port 44044
```

To start applications and register their contexts:

```sh
sentry-emulator --start ./build/my-app,label=7 --start ./build/my-other-app,label=12
```

Each started app receives `SENTRY_APP_LABEL`, `SENTRY_EMULATOR_HOST`, and
`SENTRY_EMULATOR_PORT` in its environment.

## Sample Rust tasks

The sample Rust project now builds two binaries with the same validation flow:

- `sample-app-one`
- `sample-app-two`

They are produced under `sample-rust-app/target/debug/` when building the sample
project.

## Local build

```sh
python -m build
```

## Tox workflow

```sh
tox
```
