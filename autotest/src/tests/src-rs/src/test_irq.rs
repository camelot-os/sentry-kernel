// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use crate::timer::*;
use crate::uapi::event::EventType;
use crate::uapi::status::Status;
use crate::uapi::systypes::*;
use crate::uapi::*;

static mut HANDLE: DeviceHandle = 0;

pub fn test_irq() -> bool {
    test_suite_start!("sys_irq");
    let mut ok = true;

    unsafe {
        timer_map(&mut HANDLE);
    }
    timer_init();

    ok &= test_irq_spawn_one_it();
    ok &= test_irq_spawn_two_it();
    ok &= test_irq_spawn_periodic();

    unsafe {
        timer_unmap(HANDLE);
    }

    test_suite_end!("sys_irq");
    ok
}

fn test_irq_spawn_two_it() -> bool {
    let mut ok = true;
    test_start!();

    let irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_enable();

    let mut tab = [0u8; 128];
    ok &= check_eq!(__sys_wait_for_event(EventType::Irq as u8, 0), Status::Ok);
    ok &= unsafe { copy_from_kernel(tab.as_mut_ptr(), core::mem::size_of::<ExchangeHeader>() + 4) }
        == Status::Ok;
    let irqn = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
    ok &= check_eq!(irqn, irq);

    timer_enable_interrupt();
    timer_enable();

    ok &= check_eq!(__sys_wait_for_event(EventType::Irq as u8, 0), Status::Ok);
    ok &= unsafe { copy_from_kernel(tab.as_mut_ptr(), core::mem::size_of::<ExchangeHeader>() + 4) }
        == Status::Ok;
    let irqn2 = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
    ok &= check_eq!(irqn2, irq);

    test_end!();
    ok
}
fn test_irq_spawn_one_it() -> bool {
    let mut ok = true;
    test_start!();

    let irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_enable();

    let mut tab = [0u8; 128];
    ok &= check_eq!(__sys_wait_for_event(EventType::Irq as u8, 0), Status::Ok);
    ok &= unsafe { copy_from_kernel(tab.as_mut_ptr(), core::mem::size_of::<ExchangeHeader>() + 4) }
        == Status::Ok;

    let irqn = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
    let source = u32::from_le_bytes([tab[4], tab[5], tab[6], tab[7]]);
    ok &= check_eq!(irqn, irq);
    unsafe {
        ok &= check_eq!(source, HANDLE);
    }

    test_end!();
    ok
}

fn test_irq_spawn_periodic() -> bool {
    let mut ok = true;
    test_start!();

    let irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_set_periodic();
    timer_enable();

    let mut tab = [0u8; 128];
    for count in 0..5 {
        log_info!("interrupt count {} wait", count);
        ok &= check_eq!(__sys_wait_for_event(EventType::Irq as u8, 0), Status::Ok);
        ok &= unsafe {
            copy_from_kernel(tab.as_mut_ptr(), core::mem::size_of::<ExchangeHeader>() + 4)
        } == Status::Ok;
        let irqn = u32::from_le_bytes([tab[8], tab[9], tab[10], tab[11]]);
        ok &= check_eq!(irqn, irq);
        if count < 4 {
            timer_enable_interrupt();
        }
    }

    ok &= check_eq!(
        __sys_wait_for_event(EventType::Irq as u8, 2000),
        Status::Timeout
    );

    test_end!();
    ok
}
