// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use sentry_uapi::status::Status;
use sentry_uapi::systypes::Precision;
use sentry_uapi::*;

pub fn test_random() -> bool {
    test_suite_start!("sys_get_random");
    let mut ok = true;
    ok &= test_random_sequence();
    ok &= test_random_duration();
    test_suite_end!("sys_get_random");
    ok
}

fn test_random_sequence() -> bool {
    test_start!();
    let mut ok = true;
    let mut rng: u32 = 0;
    log_info!("get back random value from KRNG");
    for _ in 0..5 {
        ok &= check_eq!(__sys_get_random(), Status::Ok);
        ok &=
            unsafe { copy_from_kernel(&mut rng as *mut _ as *mut u8, core::mem::size_of::<u32>()) }
                == Status::Ok;
        log_info!("rng retrieved: {:#010x}", rng);
    }
    test_end!();
    ok
}

fn test_random_duration() -> bool {
    let mut ok = true;
    let mut start: u64 = 0;
    let mut stop: u64 = 0;
    let mut rng: u32 = 0;
    let mut idx: u32 = 0;

    ok &= check_eq!(__sys_sched_yield(), Status::Ok);
    ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
    ok &= unsafe { copy_from_kernel(&mut start as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    for _ in 0..=1000 {
        ok &= check_eq!(__sys_get_random(), Status::Ok);
        ok &=
            unsafe { copy_from_kernel(&mut rng as *mut _ as *mut u8, core::mem::size_of::<u32>()) }
                == Status::Ok;
        idx += 1;
    }

    ok &= check_eq!(__sys_get_cycle(Precision::Microseconds), Status::Ok);
    ok &= unsafe { copy_from_kernel(&mut stop as *mut _ as *mut u8, core::mem::size_of::<u64>()) }
        == Status::Ok;

    if idx > 0 {
        log_info!(
            "average get_random+copy cost: {} µs",
            ((stop - start) / idx as u64) as u32
        );
    }

    ok
}
