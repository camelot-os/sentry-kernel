// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use uapi::syscall::*;
use uapi::systypes::Status;

fn test_yield_multiple_times() {
    for _ in 0..3 {
        let res = sched_yield();
        assert_eq!(res, Status::Ok);
    }
}

pub fn test_yield() {
    test_yield_multiple_times();
}
