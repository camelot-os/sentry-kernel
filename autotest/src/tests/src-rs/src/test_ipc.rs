// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::test_log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use core::prelude::v1::Ok;
use sentry_uapi::syscall::get_process_handle;
use sentry_uapi::syscall::send_ipc;
use sentry_uapi::syscall::wait_for_event;
use sentry_uapi::systypes::EventType;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::{ExchangeHeader, TaskHandle};
use sentry_uapi::*;

const CONFIG_SVC_EXCHANGE_AREA_LEN: usize = 128; // Should be imported from config

#[unsafe(no_mangle)]
pub extern "C" fn test_ipc() -> bool {
    test_suite_start!("sys_ipc");
    let mut ok = true;
    ok &= test_ipc_sendrecv();
    ok &= test_ipc_send_invalidtarget();
    ok &= test_ipc_send_toobig();
    ok &= test_ipc_deadlock();
    test_suite_end!("sys_ipc");
    ok
}

fn test_ipc_send_toobig() -> bool {
    test_start!();
    let mut ok = true;
    let mut handle: TaskHandle = 0;
    let len1 = CONFIG_SVC_EXCHANGE_AREA_LEN + 1;
    let len2 = 255;
    ok &= check_eq!(get_process_handle(0xbabe), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut handle as *mut _ as *mut u8)) == Ok(Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "sending invalid IPC size {}", len1);
    ok &= check_eq!(send_ipc(handle, len1 as u8), Status::Invalid);
    log_line!(USER_AUTOTEST_INFO, "sending invalid IPC size {}", len2);
    ok &= check_eq!(send_ipc(handle, len2), Status::Invalid);
    test_end!();
    ok
}
fn test_ipc_send_invalidtarget() -> bool {
    test_start!();
    log_line!(USER_AUTOTEST_INFO, "sending IPC to invalid target");
    let ok = check_eq!(send_ipc(0xdead1001, 20), Status::Invalid);
    test_end!();
    ok
}

fn test_ipc_sendrecv() -> bool {
    test_start!();
    let mut ok = true;
    let mut handle: TaskHandle = 0;
    let timeout: i32 = 100;
    let msg = b"hello it's autotest";
    let mut data = [0u8; CONFIG_SVC_EXCHANGE_AREA_LEN];

    ok &= check_eq!(get_process_handle(0xbabe), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut handle as *mut _ as *mut u8)) == Ok(Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", handle);
    log_line!(USER_AUTOTEST_INFO, "sending IPC to myself");
    ok &= copy_to_kernel(&(msg.as_ptr() as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(send_ipc(handle, 20), Status::Ok);
    ok &= check_eq!(wait_for_event(EventType::Ipc as u8, timeout), Status::Ok);
    ok &= copy_from_kernel(&mut data.as_mut_ptr()) == Ok(Status::Ok);
    let header = unsafe { &*(data.as_ptr() as *const ExchangeHeader) };
    let content =
        &data[core::mem::size_of::<ExchangeHeader>()..core::mem::size_of::<ExchangeHeader>() + 20];
    let text = core::str::from_utf8(content).unwrap_or("<invalid utf8>");
    log_line!(
        USER_AUTOTEST_INFO,
        "{}:{}:{}:src={:#x} {}",
        header.event,
        header.length,
        header.magic,
        header.peer,
        text
    );
    test_end!();
    ok
}

fn test_ipc_deadlock() -> bool {
    test_start!();
    let mut ok = true;
    let mut handle: TaskHandle = 0;
    let msg = b"hello it's autotest";

    ok &= check_eq!(get_process_handle(0xbabe), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut handle as *mut _ as *mut u8)) == Ok(Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "sending IPC to myself");
    ok &= copy_to_kernel(&(msg.as_ptr() as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(send_ipc(handle, 20), Status::Ok);
    log_line!(
        USER_AUTOTEST_INFO,
        "sending another IPC, should lead to STATUS_DEADLK"
    );
    ok &= check_eq!(send_ipc(handle, 20), Status::Deadlk);
    test_end!();
    ok
}
