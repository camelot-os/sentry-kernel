// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use uapi::exchange::copy_from_kernel;
use uapi::syscall::*;
use uapi::systypes::Precision;
use uapi::systypes::*;

fn test_random_sequence() {
    for _ in 0..5 {
        assert_eq!(get_random(), Status::Ok);
        let mut rng: u32 = 0;
        copy_from_kernel(&mut rng).unwrap();
        println!("rng retrieved: 0x{:08x}", rng);
    }
}

fn test_random_duration() {
    let mut start: u64 = 0;
    let mut stop: u64 = 0;
    let mut rng: u32 = 0;

    sched_yield();

    assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    copy_from_kernel(&mut start).unwrap();

    for _ in 0..=1000 {
        assert_eq!(get_random(), Status::Ok);
        copy_from_kernel(&mut rng).unwrap();
    }

    assert_eq!(get_cycle(Precision::Microseconds), Status::Ok);
    copy_from_kernel(&mut stop).unwrap();

    let avg_duration = ((stop - start) / 1000) as u32;
    println!("average get_random+copy cost: {}", avg_duration);
}

pub fn test_random() {
    test_random_sequence();
    test_random_duration();
}
