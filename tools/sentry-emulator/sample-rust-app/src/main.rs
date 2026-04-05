// SPDX-License-Identifier: Apache-2.0

fn main() {
    let _ = sentry_uapi::syscall::sched_yield();
    let _ = sentry_uapi::syscall::get_random();
    let _ = sentry_uapi::syscall::unsupported();
}
