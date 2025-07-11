// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::tests::log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use sentry_uapi::syscall;
use sentry_uapi::systypes::Precision;
use sentry_uapi::systypes::Status;
use sentry_uapi::copy_from_kernel;

fn test_random_sequence() {
    let mut status: Status;
    let mut rng: u32 = 0;

    test_start!();
    log_line!(USER_AUTOTEST_INFO, "get back random value from KRNG");

    for _ in 0..5 {
        status = syscall::get_random();
        let _ = copy_from_kernel(&mut rng);
        check_eq!(status, Status::Ok);
        log_line!(USER_AUTOTEST_INFO, "rng retrieved: {:#010x}", rng);
    }

    test_end!();
}

fn test_random_duration() {
    let mut start: u64 = 0;
    let mut stop: u64 = 0;
    let mut rng: u32 = 0;
    const ITER: u32 = 1000;

    syscall::sched_yield();
    syscall::get_cycle(Precision::Microseconds);
    let _ = copy_from_kernel(&mut start);

    for _ in 0..=ITER {
        syscall::get_random();
        let _ = copy_from_kernel(&mut rng);
    }

    syscall::get_cycle(Precision::Microseconds);
    let _ = copy_from_kernel(&mut stop);

    log_line!(
        USER_AUTOTEST_INFO,
        "average get_random+copy cost: {} µs",
        ((stop - start) / ITER as u64) as u32
    );
}

pub fn run() {
    test_suite_start!("syscall::get_random");
    test_random_sequence();
    test_random_duration();
    test_suite_end!("syscall::get_random");
}
