// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

//! Binary entrypoint for sample Rust app two.
//!
//! This task plays the receiver role in emulator end-to-end tests.

/// Run receiver scenario and terminate the task context with code `0`.
fn main() {
    sentry_emulator_sample_rust_tasks::run_sample_app_two();
    let _ = sentry_uapi::syscall::exit(0);
}
