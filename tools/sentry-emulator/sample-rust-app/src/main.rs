// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0


fn main() {
    let msg = "hello from sample-rust-app";
    let _ = sentry_uapi::copy_to_kernel(&msg.as_bytes());
    let _ = sentry_uapi::syscall::log(msg.len());
}
