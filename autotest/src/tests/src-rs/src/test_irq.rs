// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::test_log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use core::prelude::v1::Ok;
use sentry_uapi::syscall::wait_for_event;
use sentry_uapi::systypes::EventType;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::*;
use sentry_uapi::*;
static mut HANDLE: DeviceHandle = 0;


unsafe extern "C" {
    pub fn timer_get_irqn() -> i8;
}
pub fn get_timer_irqn() -> i8 {
    unsafe { timer_get_irqn() }
}

unsafe extern "C" {
    pub fn timer_enable_interrupt() -> i32;
}
pub fn enable_timer_interrupt() -> i32 {
    unsafe { timer_enable_interrupt() }
}

unsafe extern "C" {
    pub fn timer_enable() -> i32;
}
pub fn enable_timer() -> i32 {
    unsafe { timer_enable() }
}

unsafe extern "C" {
    pub fn timer_set_periodic() -> i32;
}
pub fn set_periodic_timer() -> i32 {
    unsafe { timer_set_periodic() }
}

unsafe extern "C" {
    pub fn timer_map(handle: *mut DeviceHandle) -> Status;
}
pub fn map_timer(handle: *mut DeviceHandle) -> Status {
    unsafe { timer_map(handle) }
}
unsafe extern "C" {
    pub fn timer_unmap(handle: DeviceHandle) -> Status;
}

pub fn unmap_timer(handle: DeviceHandle) -> Status {
    unsafe { timer_unmap(handle) }
}

unsafe extern "C" {
    pub fn timer_init() -> i32;
}
pub fn init_timer() -> i32 {
    unsafe { timer_init() }
}

#[unsafe(no_mangle)]
pub extern "C" fn test_irq() -> bool {
    test_suite_start!("sys_irq");
    let mut ok = true;
    map_timer(&raw mut HANDLE);
    init_timer();

    ok &= test_irq_spawn_one_it();
    ok &= test_irq_spawn_two_it();
    ok &= test_irq_spawn_periodic();

    unmap_timer(unsafe {HANDLE} );


    test_suite_end!("sys_irq");
    ok
}

fn test_irq_spawn_two_it() -> bool {
    let mut ok = true;
    test_start!();

    let irq = get_timer_irqn();
    enable_timer_interrupt();
    enable_timer();

    let mut tab = [0u8; 128];
    ok &= check_eq!(wait_for_event(EventType::Irq as u8, 0), Status::Ok);
    ok &= copy_from_kernel(&mut tab.as_mut_ptr()) == Ok(Status::Ok);
    let irqn = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
    ok &= check_eq!(irqn, irq as u32);

    enable_timer_interrupt();
    enable_timer();

    ok &= check_eq!(wait_for_event(EventType::Irq as u8, 0), Status::Ok);
    ok &= copy_from_kernel(&mut tab.as_mut_ptr()) == Ok(Status::Ok);
    let irqn2 = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
    ok &= check_eq!(irqn2, irq as u32);

    test_end!();
    ok
}
fn test_irq_spawn_one_it() -> bool {
    let mut ok = true;
    test_start!();

    let irq = get_timer_irqn();
    enable_timer_interrupt();
    enable_timer();

    let mut tab = [0u8; 128];
    ok &= check_eq!(wait_for_event(EventType::Irq as u8, 0), Status::Ok);
    ok &= copy_from_kernel(&mut tab.as_mut_ptr()) == Ok(Status::Ok);

    let irqn = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
    let source = u32::from_le_bytes([tab[4], tab[5], tab[6], tab[7]]);
    ok &= check_eq!(irqn, irq as u32);
    unsafe {
        ok &= check_eq!(source, unsafe { HANDLE });
    }

    test_end!();
    ok
}

fn test_irq_spawn_periodic() -> bool {
    let mut ok = true;
    test_start!();

    let irq = get_timer_irqn();
    enable_timer_interrupt();
    set_periodic_timer();
    enable_timer();

    let mut tab = [0u8; 128];
    for count in 0..5 {
        log_line!(USER_AUTOTEST_INFO, "interrupt count {} wait", count);
        ok &= check_eq!(wait_for_event(EventType::Irq as u8, 0), Status::Ok);
        ok &= copy_from_kernel(&mut tab.as_mut_ptr()) == Ok(Status::Ok);
        let irqn = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
        ok &= check_eq!(irqn, irq as u32);
        if count < 4 {
            enable_timer_interrupt();
        }
    }

    ok &= check_eq!(wait_for_event(EventType::Irq as u8, 2000), Status::Timeout);

    test_end!();
    ok
}
