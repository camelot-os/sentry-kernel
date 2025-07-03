// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check;
use crate::check_eq;
use crate::log_line;
use crate::test_start;
use crate::test_end;
use crate::test_suite_end;
use crate::test_suite_start;
use crate::tests::log::USER_AUTOTEST_INFO;


use sentry_uapi::syscall;
use sentry_uapi::systypes::{SleepDuration, Status, SleepMode, Precision};
use sentry_uapi::copy_from_kernel;

fn test_sleep_return() {
    test_start!();
    let duration = SleepDuration::ArbitraryMs(1000);
    let res = syscall::sleep(duration, SleepMode::Deep);
    assert_eq!(res, Status::Timeout);
    test_end!();
}

fn test_sleep_duration() {
    let durations = [1000u32, 100, 2000, 50, 20, 10];

    for &ms in &durations {
        test_start!();
        let duration = SleepDuration::ArbitraryMs(ms);

        let mut start: u64 = 0;
        let mut stop: u64 = 0;

        let start_status = syscall::get_cycle(Precision::Milliseconds);
        copy_from_kernel(&mut start);

        let sleep_status = syscall::sleep(duration, SleepMode::Deep);


        let stop_status = syscall::get_cycle(Precision::Milliseconds);
        copy_from_kernel(&mut stop);

        check_eq!(stop_status, Status::Ok);
        check_eq!(sleep_status, Status::Timeout);
        check_eq!(start_status, Status::Ok);
        let elapsed = (stop - start) as u32;
        check!(
            elapsed >= ms && elapsed <= ms + 1,
            "Expected sleep around {}ms, got {}ms",
            ms,
            elapsed
        );
        test_end!();
    }
}

pub fn run() {
    test_suite_start!("syscall::sleep");
    test_sleep_return();
    test_sleep_duration();
    test_suite_end!("syscall::sleep");
}
