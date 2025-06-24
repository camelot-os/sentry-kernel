// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check;
use crate::check_eq;
use crate::log_line;
use sentry_uapi::syscall::*;
use sentry_uapi::systypes::SleepDuration;
use sentry_uapi::systypes::*;
use sentry_uapi::*;

fn test_sleep_return() {
    let duration = SleepDuration::ArbitraryMs(1000);
    let res = sleep(duration, SleepMode::Deep);
    assert_eq!(res, Status::Timeout);
}

fn test_sleep_duration() {
    let durations = [1000u32, 100, 2000, 50, 20, 10];

    for &ms in &durations {
        let duration = SleepDuration::ArbitraryMs(ms);

        let mut start: u64 = 0;
        let mut stop: u64 = 0;

        let start_status = get_cycle(Precision::Milliseconds);
        check_eq!(start_status, Status::Ok);
        copy_from_kernel(&mut start).unwrap();

        let sleep_status = sleep(duration, SleepMode::Deep);
        check_eq!(sleep_status, Status::Timeout);

        let stop_status = get_cycle(Precision::Milliseconds);
        check_eq!(stop_status, Status::Ok);
        copy_from_kernel(&mut stop).unwrap();

        let elapsed = (stop - start) as u32;
        check!(
            elapsed >= ms && elapsed <= ms + 1,
            "Expected sleep around {}ms, got {}ms",
            ms,
            elapsed
        );
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn test_sleep() {
    test_sleep_return();
    test_sleep_duration();
}
