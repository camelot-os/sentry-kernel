// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::check_eq;
use sentry_uapi::*;
use crate::test_suite_start;
use crate::test_suite_end;
use crate::tests::devices_utils::get_device_by_name;
use crate::tests::log::USER_AUTOTEST_INFO;

pub fn run() -> bool {
    test_suite_start!("sys_gpio");
    let mut ok = true;

    ok &= test_gpio_toggle();
    ok &= test_gpio_off();
    syscall::sleep(systypes::SleepDuration::ArbitraryMs(1000), systypes::SleepMode::Deep);
    ok &= test_gpio_on();
    syscall::sleep(systypes::SleepDuration::ArbitraryMs(1000), systypes::SleepMode::Deep);
    ok &= test_gpio_off();
    ok &= test_gpio_invalid_io();
    ok &= test_gpio_invalid_devh();

    test_suite_end!("sys_gpio");
    ok
}

fn test_gpio_on() -> bool {
    test_start!();
    let mut dev: systypes::DeviceHandle = 0;
    let mut ok = true;
    let device = get_device_by_name("led0").expect("LED0 device not found");
    let status = syscall::get_device_handle(device.id as u8);
    let _ = copy_from_kernel(&mut dev);
    ok &= check_eq!(status, systypes::Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", dev);
    ok &= check_eq!(syscall::gpio_configure(dev, 0), systypes::Status::Ok);
    ok &= check_eq!(syscall::gpio_set(dev, 0, true), systypes::Status::Ok);
    test_end!();
    ok
}

fn test_gpio_off() -> bool {
    test_start!();
    let mut dev: systypes::DeviceHandle = 0;
    let device = get_device_by_name("led0").expect("LED0 device not found");
    let status = syscall::get_device_handle(device.id as u8);
    let _ = copy_from_kernel(&mut dev);
    let mut ok = true;
    ok &= check_eq!(status, systypes::Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", dev);
    ok &= check_eq!(syscall::gpio_configure(dev, 0), systypes::Status::Ok);
    ok &= check_eq!(syscall::gpio_set(dev, 0, false), systypes::Status::Ok);
    test_end!();
    ok
}

fn test_gpio_toggle() -> bool {
    test_start!();
    let mut dev: systypes::DeviceHandle = 0;
    let mut status;
    let mut ok = true;

    let device = get_device_by_name("led0").expect("LED0 device not found");
    status = syscall::get_device_handle(device.id as u8);
    let _ = copy_from_kernel(&mut dev);

    check_eq!(status, systypes::Status::Ok);
    check_eq!(syscall::gpio_configure(dev, 0), systypes::Status::Ok);
        for _ in 0..10 {
            ok &= check_eq!(syscall::gpio_toggle(dev, 0), systypes::Status::Ok);
            status = syscall::sleep(systypes::SleepDuration::ArbitraryMs(250u32), systypes::SleepMode::Deep);
            check_eq!(status, systypes::Status::Timeout);
        }
        test_end!();
        ok
    }

    fn test_gpio_invalid_io() -> bool {
        test_start!();
        let mut dev: systypes::DeviceHandle = 0;
        let status;
        let mut ok = true;
        let device = get_device_by_name("led0").expect("LED0 device not found");

        status = syscall::get_device_handle(device.id as u8);
        let _ = copy_from_kernel(&mut dev);

        ok &= check_eq!(status, systypes::Status::Ok);
        ok &= check_eq!(syscall::gpio_configure(dev, 4), systypes::Status::Invalid);
        ok &= check_eq!(syscall::gpio_configure(dev, 8), systypes::Status::Invalid);
        ok &= check_eq!(syscall::gpio_configure(dev, 250), systypes::Status::Invalid);
        test_end!();
        ok
    }

    fn test_gpio_invalid_devh() -> bool {
        test_start!();
        let dev: systypes::DeviceHandle = 1;
        let ok = check_eq!(syscall::gpio_configure(dev, 1), systypes::Status::Invalid);
        test_end!();
        ok
    }
