// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use sentry_uapi::*;
use sentry_uapi::status::Status;

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
struct KTaskHandle {
    rerun: u32,
    id: u8,
    family: u8,
}

impl KTaskHandle {
    fn from_raw(raw: TaskHandle) -> Self {
        let rerun = raw & 0xFFFFF; // 20 bits
        let id = ((raw >> 20) & 0xFF) as u8; // next 8 bits
        let family = ((raw >> 28) & 0x7) as u8; // next 3 bits
        KTaskHandle { rerun, id, family }
    }
}

pub fn test_handle() -> bool {
    test_suite_start!("sys_get_handle");
    let ok = test_gethandle();
    test_suite_end!("sys_get_handle");
    ok
}
fn test_gethandle() -> bool {
    test_start!();
    let mut handle: TaskHandle = 0;
    let mut ok = true;

    unsafe {
        ok &= copy_to_kernel(&mut handle as *mut _ as *mut u8, core::mem::size_of::<TaskHandle>()) == Status::Ok;
    }
    unsafe {
        ok &= copy_from_kernel(&mut handle as *mut _ as *mut u8, core::mem::size_of::<TaskHandle>()) == Status::Ok;
    }
    ok &= check_eq!(handle, 0);

    ok &= check_eq!(__sys_get_process_handle(0xbabe), Status::Ok);
    unsafe {
        ok &= copy_from_kernel(&mut handle as *mut _ as *mut u8, core::mem::size_of::<TaskHandle>()) == Status::Ok;
    }
    log_info!("received handle: {:#x}", handle);

    let khandle = KTaskHandle::from_raw(handle);
    log_info!("handle rerun = {:#x}", khandle.rerun);
    log_info!("handle id = {:#x}", khandle.id);
    log_info!("handle family = {:#x}", khandle.family);

    test_end!();
    ok
}
