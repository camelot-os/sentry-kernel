// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::device_utils::get_device_by_name;
use crate::devices::*;
use crate::test_end;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use crate::log_line;
use crate::test_log::USER_AUTOTEST_INFO;
use core::prelude::v1::Ok;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::*;
use sentry_uapi::*;

pub fn test_map() -> bool {
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
    let mut dev: DeviceHandle = 0;
    let ok = check_eq!(__sys_get_device_handle(device.id as u8), Status::Ok)
        & unsafe { copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) }
        == Ok(Status::Ok) & check_eq!(__sys_unmap_dev(dev), Status::Invalid);
    test_end!();
    ok
}

fn test_map_invalidmap() -> bool {
    test_start!();
    let device = get_device_by_name("i2c1").expect("i2c1 device not found");
    let mut dev: DeviceHandle = 0;
    let ok = check_eq!(__sys_get_device_handle(device.id as u8), Status::Ok)
        & unsafe { copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) }
        == Ok(Status::Ok);
    let invalid_dev = dev.wrapping_add(42);
    let ok = ok & check_eq!(__sys_map_dev(invalid_dev), Status::Invalid);
    test_end!();
    ok
}

fn test_map_mapunmap() -> bool {
    test_start!();
    let device = get_device_by_name("i2c1").expect("i2c1 device not found");
    let mut dev: DeviceHandle = 0;
    let mut ok = check_eq!(__sys_get_device_handle(device.id as u8), Status::Ok)
        & unsafe { copy_from_kernel(&mut (&mut dev as *mut _ as *mut u8)) }
        == Ok(Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", dev);
    ok &= check_eq!(__sys_map_dev(dev), Status::Ok);

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
    ok &= check_eq!(__sys_unmap_dev(dev), Status::Ok);
    test_end!();
    ok
}
