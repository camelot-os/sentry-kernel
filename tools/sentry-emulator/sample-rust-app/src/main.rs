// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0


fn main() {
    let _ = sentry_uapi::syscall::sched_yield();
    let _ = sentry_uapi::syscall::get_random();
    let _ = sentry_uapi::syscall::unsupported();
}
