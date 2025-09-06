// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::tests::log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;

use sentry_uapi::syscall;
use sentry_uapi::systypes;

const CONFIG_SVC_EXCHANGE_AREA_LEN: usize = 128; // Should be imported from config

pub fn run() -> bool {
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
    let status;
    let mut handle: systypes::TaskHandle = 0;

    let len1 = CONFIG_SVC_EXCHANGE_AREA_LEN + 1;
    let len2 = 255;
    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut handle);
    ok &= check_eq!(status, systypes::Status::Ok);

    log_line!(USER_AUTOTEST_INFO, "sending invalid IPC size {}", len1);
    ok &= check_eq!(syscall::send_ipc(handle, len1 as u8), systypes::Status::Invalid);
    log_line!(USER_AUTOTEST_INFO, "sending invalid IPC size {}", len2);
    ok &= check_eq!(syscall::send_ipc(handle, len2), systypes::Status::Invalid);
    test_end!();
    ok
}

fn test_ipc_send_invalidtarget() -> bool {
    test_start!();
    let mut ok = true;
    let status;
    log_line!(USER_AUTOTEST_INFO, "sending IPC to invalid target");
    status = syscall::send_ipc(0xdead1001, 20);
    ok &= check_eq!(status, systypes::Status::Invalid);
    test_end!();
    ok
}


fn test_ipc_sendrecv() -> bool {
    test_start!();
    let mut ok = true;
    let mut status;
    let mut handle: systypes::TaskHandle = 0;
    let timeout: i32 = 100;
    let msg = "hello it's autotest";
    let mut data = [0u8; CONFIG_SVC_EXCHANGE_AREA_LEN];

    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut handle);
    ok &= check_eq!(status, systypes::Status::Ok);

    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", handle);
    log_line!(USER_AUTOTEST_INFO, "sending IPC to myself");

    // Emit IPC
    let _ = sentry_uapi::copy_to_kernel(&(msg.as_bytes()));
    status = syscall::send_ipc(handle, 20);
    ok &= check_eq!(status, systypes::Status::Ok);
    // Recive IPC
    status = syscall::wait_for_event(systypes::EventType::Ipc as u8, timeout);
    ok &= sentry_uapi::copy_from_kernel(&mut (&mut data[..])) == Ok(systypes::Status::Ok);
    assert_eq!(status, systypes::Status::Ok);

    let header = unsafe { &*(data.as_ptr() as *const systypes::ExchangeHeader) };
    let content =
        &data[core::mem::size_of::<systypes::ExchangeHeader>()..core::mem::size_of::<systypes::ExchangeHeader>() + 20];
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
    let mut handle: systypes::TaskHandle = 0;
    let status;
    let msg = "hello it's autotest";

    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut handle);

    assert_eq!(status, systypes::Status::Ok);

    log_line!(USER_AUTOTEST_INFO, "sending IPC to myself");
    let _ = sentry_uapi::copy_to_kernel(&(msg.as_bytes()));
    ok &= check_eq!(syscall::send_ipc(handle, 20), systypes::Status::Ok);
    log_line!(
        USER_AUTOTEST_INFO,
        "sending another IPC, should lead to STATUS_DEADLK"
    );
    ok &= check_eq!(syscall::send_ipc(handle, 20), systypes::Status::Deadlk);
    test_end!();
    ok
}
