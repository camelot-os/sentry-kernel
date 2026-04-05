// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

fn main() {
    sentry_emulator_sample_rust_tasks::run_sample_app_one(8);
    let _ = sentry_uapi::syscall::exit(0);
}
