// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use uapi::syscall::*;
use uapi::exchange::copy_from_kernel;
use uapi::systypes::*;
use uapi::devices::{DEVICE_ID, DEV_ID_LED0};

fn test_gpio_on() {
    let mut dev: DeviceHandle = 0;
    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_LED0]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();

    assert_eq!(gpio_configure(dev, 0), Status::Ok);
    assert_eq!(gpio_set(dev, 0, true), Status::Ok);
}

fn test_gpio_off() {
    let mut dev: DeviceHandle = 0;
    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_LED0]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();

    assert_eq!(gpio_configure(dev, 0), Status::Ok);
    assert_eq!(gpio_set(dev, 0, false), Status::Ok);
}

fn test_gpio_toggle() {
    let mut dev: DeviceHandle = 0;
    let duration = SleepDuration::ArbitraryMs(250);

    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_LED0]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();

    assert_eq!(gpio_configure(dev, 0), Status::Ok);

    for _ in 0..10 {
        assert_eq!(gpio_toggle(dev, 0), Status::Ok);
        assert_eq!(sleep(duration, SleepMode::Deep), Status::Timeout);
    }
}

fn test_gpio_invalid_io() {
    let mut dev: DeviceHandle = 0;
    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_LED0]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();

    assert_eq!(gpio_configure(dev, 4), Status::Invalid);
    assert_eq!(gpio_configure(dev, 8), Status::Invalid);
    assert_eq!(gpio_configure(dev, 250), Status::Invalid);
}

fn test_gpio_invalid_devh() {
    let dev: DeviceHandle = 1;
    assert_eq!(gpio_configure(dev, 1), Status::Invalid);
}

pub fn test_gpio() {
    test_gpio_on();
    test_gpio_off();
    test_gpio_toggle();
    test_gpio_invalid_io();
    test_gpio_invalid_devh();
}
