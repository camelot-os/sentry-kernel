// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check;
use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::tests::log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;

use core::prelude::v1::Ok;

use sentry_uapi::syscall;
use sentry_uapi::systypes::Precision;
use sentry_uapi::systypes::Status;
use sentry_uapi;

pub fn run() -> bool {
    test_suite_start!("sys_cycles");
    let mut ok = true;
    ok &= test_cycles_duration();
    ok &= test_cycles_precision();
    test_suite_end!("sys_cycles");
    ok
}

fn test_cycles_duration() -> bool {
    test_start!();
    let mut ok = true;

    let mut start: u64 = 0u64;

    let mut stop: u64 = 0u64;
    let mut micro: u64 = 0;

    // let mut idx = 0u32;
    let iter: u64 = 1000;

    let _ = syscall::sched_yield();
    let _ = syscall::get_cycle(Precision::Microseconds);

    check_eq!(sentry_uapi::copy_from_kernel(&mut start), Ok::<Status, Status>(Status::Ok));

    for _ in 0..=iter {
        let _ = syscall::get_cycle(Precision::Microseconds);
    }

    ok &= syscall::get_cycle(Precision::Microseconds) == Status::Ok;
    ok &= sentry_uapi::copy_from_kernel(&mut stop) == Ok(Status::Ok);

    log_line!(
        USER_AUTOTEST_INFO,
        "average get_cycle cost: {}",
        ((stop - start) / iter as u64) as u32
    );

    let _ = syscall::sched_yield();
    let _ = syscall::get_cycle(Precision::Microseconds);
    let _ = syscall::sched_yield();
    let _ = sentry_uapi::copy_from_kernel(&mut start);
    for _ in 0..=iter {
        let _ = syscall::get_cycle(Precision::Microseconds);
        let _ = sentry_uapi::copy_from_kernel(&mut micro);
    }

    let _ = syscall::get_cycle(Precision::Microseconds);
    let _ = sentry_uapi::copy_from_kernel(&mut stop);

    log_line!(
        USER_AUTOTEST_INFO,
        "average get_cycle+copy cost: {}",
        ((stop - start) / iter as u64) as u32
    );
    test_end!();
    ok
}
fn test_cycles_precision() -> bool {
    test_start!();
    let mut ok = true;
    let mut milli: u64 = 0;
    let mut micro: u64 = 0;
    let mut nano: u64 = 0;

    let milli_st = syscall::get_cycle(Precision::Milliseconds);
    ok &= sentry_uapi::copy_from_kernel(&mut milli) == Ok(Status::Ok);

    let micro_st = syscall::get_cycle(Precision::Microseconds);
    ok &= sentry_uapi::copy_from_kernel(&mut micro) == Ok(Status::Ok);

    let nano_st = syscall::get_cycle(Precision::Nanoseconds);
    ok &= sentry_uapi::copy_from_kernel(&mut nano) == Ok(Status::Ok);

    let cycle_st = syscall::get_cycle(Precision::Cycle);

    ok &= check_eq!(milli_st, Status::Ok);
    ok &= check!(milli as u32 > 0, "milli > 0");

    ok &= check_eq!(micro_st, Status::Ok);
    ok &= check!(micro * 1000 > milli, "micro*1000 > milli");

    ok &= check_eq!(nano_st, Status::Ok);
    ok &= check!(nano * 1000 > micro, "nano*1000 > micro");

    ok &= check_eq!(cycle_st, Status::Denied);

    test_end!();
    ok
}
