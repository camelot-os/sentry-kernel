// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use uapi::exchange::copy_from_kernel;
use uapi::syscall::*;
use uapi::systypes::SleepDuration;
use uapi::systypes::*;

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
        assert_eq!(start_status, Status::Ok);
        copy_from_kernel(&mut start).unwrap();

        let sleep_status = sleep(duration, SleepMode::Deep);
        assert_eq!(sleep_status, Status::Timeout);

        let stop_status = get_cycle(Precision::Milliseconds);
        assert_eq!(stop_status, Status::Ok);
        copy_from_kernel(&mut stop).unwrap();

        let elapsed = (stop - start) as u32;
        assert!(
            elapsed >= ms && elapsed <= ms + 1,
            "Expected sleep around {}ms, got {}ms",
            ms,
            elapsed
        );
    }
}

pub fn test_sleep() {
    test_sleep_return();
    test_sleep_duration();
}
