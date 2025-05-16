// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use uapi::syscall::*;
use uapi::exchange::copy_from_kernel;
use uapi::systypes::{Status, Precision};

fn test_cycles_duration() {
    let mut start: u64 = 0;
    let mut stop: u64 = 0;
    let mut tmp: u64 = 0;
    let mut idx = 0;

    
    assert_eq!(sched_yield(), Status::Ok);

    assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    copy_from_kernel(&mut start).unwrap();

    for _ in 0..=1000 {
        assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    }

    assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    copy_from_kernel(&mut stop).unwrap();

    let avg_cost = ((stop - start) / 1000) as u32;
    println!("average get_cycle cost: {}", avg_cost);

    // Deuxième boucle avec `copy_from_kernel` à chaque appel
    assert_eq!(sched_yield(), Status::Ok);
    assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    copy_from_kernel(&mut start).unwrap();

    for _ in 0..=1000 {
        assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
        copy_from_kernel(&mut tmp).unwrap();
    }

    assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    copy_from_kernel(&mut stop).unwrap();

    let avg_copy_cost = ((stop - start) / 1000) as u32;
    println!("average get_cycle + copy cost: {}", avg_copy_cost);
}

fn test_cycles_precision() {
    let mut milli: u64 = 0;
    let mut micro: u64 = 0;
    let mut nano: u64 = 0;

    let milli_st = get_cycle(Precision::Milliseconds);
    copy_from_kernel(&mut milli).unwrap();

    let micro_st = get_cycle(Precision::Microseconds);
    copy_from_kernel(&mut micro).unwrap();

    let nano_st = get_cycle(Precision::Nanoseconds);
    copy_from_kernel(&mut nano).unwrap();

    let cycle_st = get_cycle(Precision::Cycle);

    assert_eq!(milli_st, Status::Ok);
    assert!(milli > 0);

    assert_eq!(micro_st, Status::Ok);
    assert!((micro * 1000) > milli);

    assert_eq!(nano_st, Status::Ok);
    assert!((nano * 1000) > micro);

    assert_eq!(cycle_st, Status::Denied);
}

pub fn test_cycles() {
    test_cycles_duration();
    test_cycles_precision();
}
