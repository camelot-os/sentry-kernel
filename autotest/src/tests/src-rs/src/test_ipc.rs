// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use crate::uapi::event::EventType;
use crate::uapi::status::Status;
use crate::uapi::systypes::{ExchangeHeader, TaskHandle};
use crate::uapi::*;

pub fn test_ipc() -> bool {
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
    ok &= check_eq!(__sys_get_process_handle(0xbabe), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut handle as *mut _ as *mut u8,
            core::mem::size_of::<TaskHandle>(),
        )
    } == Status::Ok;
    log_info!("sending invalid IPC size {}", len1);
    ok &= check_eq!(__sys_send_ipc(handle, len1 as u8), Status::Invalid);
    log_info!("sending invalid IPC size {}", len2);
    ok &= check_eq!(__sys_send_ipc(handle, len2), Status::Invalid);
    test_end!();
    ok
}
fn test_ipc_send_invalidtarget() -> bool {
    test_start!();
    log_info!("sending IPC to invalid target");
    let ok = check_eq!(__sys_send_ipc(0xdead1001, 20), Status::Invalid);
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

    ok &= check_eq!(__sys_get_process_handle(0xbabe), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut handle as *mut _ as *mut u8,
            core::mem::size_of::<TaskHandle>(),
        )
    } == Status::Ok;
    log_info!("handle is {:#x}", handle);
    log_info!("sending IPC to myself");
    unsafe {
        ok &= copy_to_kernel(msg.as_ptr() as *mut u8, msg.len()) == Status::Ok;
    }
    ok &= check_eq!(__sys_send_ipc(handle, 20), Status::Ok);
    ok &= check_eq!(
        __sys_wait_for_event(EventType::Ipc as u8, timeout),
        Status::Ok
    );
    ok &= unsafe {
        copy_from_kernel(
            data.as_mut_ptr(),
            20 + core::mem::size_of::<ExchangeHeader>(),
        ) == Status::Ok
    };
    let header = unsafe { &*(data.as_ptr() as *const ExchangeHeader) };
    let content =
        &data[core::mem::size_of::<ExchangeHeader>()..core::mem::size_of::<ExchangeHeader>() + 20];
    let text = core::str::from_utf8(content).unwrap_or("<invalid utf8>");
    log_info!(
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

    ok &= check_eq!(__sys_get_process_handle(0xbabe), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut handle as *mut _ as *mut u8,
            core::mem::size_of::<TaskHandle>(),
        )
    } == Status::Ok;
    log_info!("sending IPC to myself");
    unsafe {
        ok &= copy_to_kernel(msg.as_ptr() as *mut u8, msg.len()) == Status::Ok;
    }
    ok &= check_eq!(__sys_send_ipc(handle, 20), Status::Ok);
    log_info!("sending another IPC, should lead to STATUS_DEADLK");
    ok &= check_eq!(__sys_send_ipc(handle, 20), Status::Deadlk);
    test_end!();
    ok
}
