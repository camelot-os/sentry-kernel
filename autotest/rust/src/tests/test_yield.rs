// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use crate::test_start;
use crate::test_end;
use crate::test_suite_end;
use crate::test_suite_start;
use crate::tests::log::USER_AUTOTEST_INFO;

use sentry_uapi::syscall;
use sentry_uapi::systypes::Status;

fn test_yield_multiple_times() {
    test_start!();
    for _ in 0..3 {
        log_line!(USER_AUTOTEST_INFO, "yielding...");
        let res = syscall::sched_yield();
        check_eq!(res, Status::Ok);
    }
    test_end!();
}

pub fn run() {
    test_suite_start!("sys_yield");
    test_yield_multiple_times();
    test_suite_end!("sys_yield");
}
