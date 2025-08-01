// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::check_eq;
use sentry_uapi::*;
use crate::test_suite_start;
use crate::test_suite_end;
use crate::tests::log::USER_AUTOTEST_INFO;

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
struct KTaskHandle {
    rerun: u32,
    id: u8,
    family: u8,
}

impl KTaskHandle {
    fn from_raw(raw: systypes::TaskHandle) -> Self {
        let rerun = raw & 0xFFFFF; // 20 bits
        let id = ((raw >> 20) & 0xFF) as u8; // next 8 bits
        let family = ((raw >> 28) & 0x7) as u8; // next 3 bits
        KTaskHandle { rerun, id, family }
    }
}

pub fn run() -> bool {
    test_suite_start!("sys_get_handle");
    let ok = test_gethandle();
    test_suite_end!("sys_get_handle");
    ok
}

fn test_gethandle() -> bool {
    test_start!();
    let mut handle: systypes::TaskHandle = 0;
    let mut ok = true;
    let status : systypes::Status;

    status = syscall::get_process_handle(0xbabe);
    let _ = copy_from_kernel(&mut handle);
    ok &= check_eq!(status, systypes::Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", handle);

    let khandle = KTaskHandle::from_raw(handle);
    //log_line!(USER_AUTOTEST_INFO, "handle rerun = {:#x}", khandle.rerun);
    log_line!(USER_AUTOTEST_INFO, "id = {:#x}", khandle.id);
    log_line!(USER_AUTOTEST_INFO, "family = {:#x}", khandle.family);

    test_end!();
    ok
}
