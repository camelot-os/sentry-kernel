// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::tests::devices_utils::get_device_by_name;
use crate::log_line;
use crate::test_end;
use crate::tests::log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use sentry_uapi::syscall;
use sentry_uapi::systypes;

pub fn run() -> bool {
    test_suite_start!("sys_map");
    let mut ok = true;
    ok &= test_map_mapunmap();
    ok &= test_map_invalidmap();
    ok &= test_map_unmap_notmapped();
    test_suite_end!("sys_map");
    ok
}

fn test_map_unmap_notmapped() -> bool {
    test_start!();
    // This will fail if the i2c1 is not found
    let device = get_device_by_name("i2c1").expect("i2c1 device not found");
    let mut dev: systypes::DeviceHandle = 0;
    let mut ok = true;
    let mut status : systypes::Status;

    status = syscall::get_device_handle(device.id);
    let _ = sentry_uapi::copy_from_kernel(& mut dev);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::unmap_dev(dev);
    ok &= check_eq!(status, systypes::Status::Invalid);

    test_end!();
    ok
}

fn test_map_invalidmap() -> bool {
    test_start!();

    let device = get_device_by_name("i2c1").expect("i2c1 device not found");
    let mut dev: systypes::DeviceHandle = 0;
    let mut ok : bool = true;
    let mut status : systypes::Status;

    status = syscall::get_device_handle(device.id);
    let _ = sentry_uapi::copy_from_kernel(& mut dev);

    ok &= check_eq!(status, systypes::Status::Ok);
    status = syscall::map_dev(dev + 42);

    ok &= check_eq!(status, systypes::Status::Invalid);

    test_end!();
    ok
}

fn test_map_mapunmap() -> bool {
    test_start!();

    let device = get_device_by_name("i2c1").expect("i2c1 device not found");
    let mut dev: systypes::DeviceHandle = 0;
    let mut ok = true;
    let mut status : systypes::Status;


    status = syscall::get_device_handle(device.id);
    let _ = sentry_uapi::copy_from_kernel(&mut dev);
    ok &= check_eq!(status, systypes::Status::Ok);

    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", dev);

    status = syscall::map_dev(dev);
    ok &= check_eq!(status, systypes::Status::Ok);

    // stm32u5a5 has a known register map that is used to check the mapping
    // read access to the registers
    #[cfg(CONFIG_ARCH_MCU_STM32U5A5)]
    if ok {
        log_line!(USER_AUTOTEST_INFO, "device mapped, checking registers");
        let base = device.baseaddr;
        for offset in (0..12 * 4).step_by(4) {
            let val = unsafe { core::ptr::read_volatile((base + offset as usize) as *const u32) };
            if offset != 6 * 4 {
                ok &= check_eq!(val, 0x0);
            } else {
                ok &= check_eq!(val, 0x1);
            }
        }
    }

    log_line!(USER_AUTOTEST_INFO, "unmapping");
    status = syscall::unmap_dev(dev);
    ok &= check_eq!(status, systypes::Status::Ok);

    test_end!();
    ok
}
