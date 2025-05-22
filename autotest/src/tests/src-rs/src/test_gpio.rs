// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use crate::uapi::*;
use crate::uapi::status::Status;
use crate::uapi::systypes::{SleepDuration, SleepMode, DeviceHandle};

pub fn test_gpio() -> bool {
    test_suite_start!("sys_gpio");
    let mut ok = true;

    ok &= test_gpio_toggle();
    ok &= test_gpio_off();
    __sys_sleep(SleepDuration { tag: SLEEP_DURATION_ARBITRARY_MS, arbitrary_ms: 1000 }, SleepMode::Deep);
    ok &= test_gpio_on();
    __sys_sleep(SleepDuration { tag: SLEEP_DURATION_ARBITRARY_MS, arbitrary_ms: 1000 }, SleepMode::Deep);
    ok &= test_gpio_off();
    ok &= test_gpio_invalid_io();
    ok &= test_gpio_invalid_devh();

    test_suite_end!("sys_gpio");
    ok
}

fn test_gpio_on() -> bool {
    test_start!();
    let mut dev: DeviceHandle = 0;
    let ok = check_eq!(__sys_get_device_handle(devices[DEV_ID_LED0].id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut dev as *mut _ as *mut u8, core::mem::size_of::<DeviceHandle>()) } == Status::Ok);
    log_info!("handle is {:#x}", dev);
    let ok = ok
        & check_eq!(__sys_gpio_configure(dev, 0), Status::Ok)
        & check_eq!(__sys_gpio_set(dev, 0, true), Status::Ok);
    test_end!();
    ok
}

fn test_gpio_off() -> bool {
    test_start!();
    let mut dev: DeviceHandle = 0;
    let ok = check_eq!(__sys_get_device_handle(devices[DEV_ID_LED0].id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut dev as *mut _ as *mut u8, core::mem::size_of::<DeviceHandle>()) } == Status::Ok);
    log_info!("handle is {:#x}", dev);
    let ok = ok
        & check_eq!(__sys_gpio_configure(dev, 0), Status::Ok)
        & check_eq!(__sys_gpio_set(dev, 0, false), Status::Ok);
    test_end!();
    ok
}

fn test_gpio_toggle() -> bool {
    test_start!();
    let mut dev: DeviceHandle = 0;
    let duration = SleepDuration { tag: SLEEP_DURATION_ARBITRARY_MS, arbitrary_ms: 250 };
    let mut ok = check_eq!(__sys_get_device_handle(devices[DEV_ID_LED0].id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut dev as *mut _ as *mut u8, core::mem::size_of::<DeviceHandle>()) } == Status::Ok)
        & check_eq!(__sys_gpio_configure(dev, 0), Status::Ok);
        for _ in 0..10 {
            ok &= check_eq!(__sys_gpio_toggle(dev, 0), Status::Ok);
            __sys_sleep(duration, SleepMode::Deep);
        }
        test_end!();
        ok
    }
    
    fn test_gpio_invalid_io() -> bool {
        test_start!();
        let mut dev: DeviceHandle = 0;
        let ok = check_eq!(__sys_get_device_handle(devices[DEV_ID_LED0].id), Status::Ok)
            & (unsafe { copy_from_kernel(&mut dev as *mut _ as *mut u8, core::mem::size_of::<DeviceHandle>()) } == Status::Ok)
            & check_eq!(__sys_gpio_configure(dev, 4), Status::Invalid)
            & check_eq!(__sys_gpio_configure(dev, 8), Status::Invalid)
            & check_eq!(__sys_gpio_configure(dev, 250), Status::Invalid);
        test_end!();
        ok
    }
    
    fn test_gpio_invalid_devh() -> bool {
        test_start!();
        let dev: DeviceHandle = 1;
        let ok = check_eq!(__sys_gpio_configure(dev, 1), Status::Invalid);
        test_end!();
        ok
    }
    