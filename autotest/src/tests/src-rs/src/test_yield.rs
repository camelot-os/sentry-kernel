// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use sentry_uapi::syscall::*;
use sentry_uapi::systypes::Status;

fn test_yield_multiple_times() {
    for _ in 0..3 {
        let res = sched_yield();
        check_eq!(res, Status::Ok);
    }
}

pub fn test_yield() {
    test_yield_multiple_times();
}
