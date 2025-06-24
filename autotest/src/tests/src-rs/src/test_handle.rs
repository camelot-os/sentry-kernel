// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::check_eq;
use sentry_uapi::*;
use sentry_uapi::syscall::get_process_handle;
use sentry_uapi::systypes::Status;
use core::prelude::v1::Ok;
use crate::test_suite_start;
use sentry_uapi::systypes::TaskHandle;
use crate::test_suite_end;
use crate::test_log::USER_AUTOTEST_INFO;

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

#[unsafe(no_mangle)]
pub extern "C" fn test_handle() -> bool {
    test_suite_start!("sys_get_handle");
    let ok = test_gethandle();
    test_suite_end!("sys_get_handle");
    ok
}
fn test_gethandle() -> bool {
    test_start!();
    let mut handle: TaskHandle = 0;
    let mut ok = true;
    ok &= copy_to_kernel(&mut (&mut handle as *mut _ as *mut u8)) == Ok(Status::Ok);
    ok &= copy_from_kernel(&mut (&mut handle as *mut _ as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(handle, 0);

    ok &= check_eq!(get_process_handle(0xbabe), Status::Ok);
  
    ok &= copy_from_kernel(&mut (&mut handle as *mut _ as *mut u8)) == Ok(Status::Ok);

    log_line!(USER_AUTOTEST_INFO, "received handle: {:#x}", handle);

    let khandle = KTaskHandle::from_raw(handle);
    //log_line!(USER_AUTOTEST_INFO, "handle rerun = {:#x}", khandle.rerun);
    log_line!(USER_AUTOTEST_INFO, "handle id = {:#x}", khandle.id);
    log_line!(USER_AUTOTEST_INFO, "handle family = {:#x}", khandle.family);

    test_end!();
    ok
}
