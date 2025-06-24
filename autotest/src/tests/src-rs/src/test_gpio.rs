// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::check_eq;
use sentry_uapi::*;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::{SleepDuration, SleepMode, DeviceHandle};
use core::prelude::v1::Ok;
use sentry_uapi::syscall::{get_device_handle, gpio_configure, gpio_set, gpio_toggle, sleep};
use crate::test_suite_start;
use crate::test_suite_end;
use crate::devices_utils::get_device_by_name;

#[unsafe(no_mangle)]
pub extern "C" fn test_gpio() -> bool {
    test_suite_start!("sys_gpio");
    let mut ok = true;

    ok &= test_gpio_toggle();
    ok &= test_gpio_off();
    sleep(SleepDuration::ArbitraryMs(1000), SleepMode::Deep);
    ok &= test_gpio_on();
    sleep(SleepDuration::ArbitraryMs(1000), SleepMode::Deep);
    ok &= test_gpio_off();
    ok &= test_gpio_invalid_io();
    ok &= test_gpio_invalid_devh();

    test_suite_end!("sys_gpio");
    ok
}

fn test_gpio_on() -> bool {
    test_start!();
    let mut dev: DeviceHandle = 0;
    let device = get_device_by_name("led0").expect("LED0 device not found");
    let ok = check_eq!(get_device_handle(device.id as u8), Status::Ok)
        & (copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) == Ok(Status::Ok));
    log_line!("USER_AUTOTEST_INFO", "handle is {:#x}", dev);
    let ok = ok
        & check_eq!(gpio_configure(dev, 0), Status::Ok)
        & check_eq!(gpio_set(dev, 0, true), Status::Ok);
    test_end!();
    ok
}

fn test_gpio_off() -> bool {
    test_start!();
    let mut dev: DeviceHandle = 0;
    let device = get_device_by_name("led0").expect("LED0 device not found");
    let ok = check_eq!(get_device_handle(device.id as u8), Status::Ok)
        & (copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) == Ok(Status::Ok));
    log_line!("USER_AUTOTEST_INFO", "handle is {:#x}", dev);
    let ok = ok
        & check_eq!(gpio_configure(dev, 0), Status::Ok)
        & check_eq!(gpio_set(dev, 0, false), Status::Ok);
    test_end!();
    ok
}

fn test_gpio_toggle() -> bool {
    test_start!();
    let mut dev: DeviceHandle = 0;
    let duration = SleepDuration::ArbitraryMs(250);
    let device = get_device_by_name("led0").expect("LED0 device not found");
    let mut ok = check_eq!(get_device_handle(device.id as u8), Status::Ok)
        & (copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) == Ok(Status::Ok))
        & check_eq!(gpio_configure(dev, 0), Status::Ok);
        let value = sleep(duration, SleepMode::Deep);
        for _ in 0..10 {
            ok &= check_eq!(gpio_toggle(dev, 0), Status::Ok);
            value;
        }
        test_end!();
        ok
    }

    fn test_gpio_invalid_io() -> bool {
        test_start!();
        let mut dev: DeviceHandle = 0;
        let device = get_device_by_name("led0").expect("LED0 device not found");

        let ok = check_eq!(get_device_handle(device.id as u8), Status::Ok)
            & (copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) == Ok(Status::Ok))
            & check_eq!(gpio_configure(dev, 4), Status::Invalid)
            & check_eq!(gpio_configure(dev, 8), Status::Invalid)
            & check_eq!(gpio_configure(dev, 250), Status::Invalid);
        test_end!();
        ok
    }

    fn test_gpio_invalid_devh() -> bool {
        test_start!();
        let dev: DeviceHandle = 1;
        let ok = check_eq!(gpio_configure(dev, 1), Status::Invalid);
        test_end!();
        ok
    }
