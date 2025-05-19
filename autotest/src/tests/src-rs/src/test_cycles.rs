// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use crate::uapi::status::Status;
use crate::uapi::systypes::{Precision, SleepDuration};
use crate::uapi::*;

pub fn test_cycles() -> bool {
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
    let mut start: u64 = 0;
    let mut stop: u64 = 0;
    let mut micro: u64 = 0;

    let mut idx = 0u32;

    ok &= check_eq!(__sys_sched_yield(), Status::Ok);
    ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
    ok &= unsafe { copy_from_kernel(&mut start as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;
    for _ in 0..=1000 {
        let _ = __sys_get_cycle(Precision::Microseconds);
        idx += 1;
    }

    ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
    ok &= unsafe { copy_from_kernel(&mut stop as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    log_info!(
        "average get_cycle cost: {}",
        ((stop - start) / idx as u64) as u32
    );

    ok &= check_eq!(__sys_sched_yield(), Status::Ok);
    ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
    ok &= unsafe { copy_from_kernel(&mut start as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    for _ in 0..=1000 {
        ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
        ok &= unsafe {
            copy_from_kernel(&mut micro as *mut _ as *mut u8, core::mem::size_of::<u64>())
        } == Status::Ok;
    }

    ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
    ok &= unsafe { copy_from_kernel(&mut stop as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    log_info!(
        "average get_cycle+copy cost: {}",
        ((stop - start) / idx as u64) as u32
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

    let milli_st = __sys_get_cycle(Precision::Milliseconds);
    ok &= unsafe { copy_from_kernel(&mut milli as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    let micro_st = __sys_get_cycle(Precision::Microseconds);
    ok &= unsafe { copy_from_kernel(&mut micro as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    let nano_st = __sys_get_cycle(Precision::Nanoseconds);
    ok &= unsafe { copy_from_kernel(&mut nano as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    let cycle_st = __sys_get_cycle(Precision::Cycle);

    ok &= check_eq!(milli_st, Status::Ok);
    ok &= check!(milli as u32 > 0, "milli > 0");

    ok &= check_eq!(micro_st, Status::Ok);
    ok &= check!(((micro * 1000) > milli), "micro*1000 > milli");

    ok &= check_eq!(nano_st, Status::Ok);
    ok &= check!(((nano * 1000) > micro), "nano*1000 > micro");

    ok &= check_eq!(cycle_st, Status::Denied);

    test_end!();
    ok
}
