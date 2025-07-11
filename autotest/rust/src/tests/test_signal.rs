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
use sentry_uapi::systypes::{EventType, ExchangeHeader, Signal, Status, TaskHandle};
use sentry_uapi::copy_from_kernel;

use core::ptr::addr_of_mut;

#[repr(C)]
#[derive(Copy, Clone)]
struct ExchangeEvent {
    header: ExchangeHeader,
    data: [u8; 4],
}

fn test_signal_sendrecv() {
    test_start!();

    let timeout: i32 = 20;
    let mut handle: TaskHandle = 0;
    let mut event = ExchangeEvent{
        header: ExchangeHeader{event: 0, length: 0, magic: 0, peer: 0},
        data: [0u8;4]
    };
    let mut buffer: &mut [u8] = unsafe {
        core::slice::from_raw_parts_mut(addr_of_mut!(*(&mut event)) as *mut u8,
        core::mem::size_of::<ExchangeEvent>()) as &mut [u8]
    };

    let status = syscall::get_process_handle(0xbabe);
    let _ = copy_from_kernel(&mut handle).unwrap();
    check_eq!(status, Status::Ok);
    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", handle);

    for sig_val in (Signal::Abort as u8)..=(Signal::Usr2 as u8) {
        let sig = unsafe { core::mem::transmute::<u8, Signal>(sig_val) };
        log_line!(USER_AUTOTEST_INFO, "sending signal {} to myself", sig as u32);

        let status = syscall::send_signal(handle, sig.clone());
        check_eq!(status, Status::Ok);

        let status = syscall::wait_for_event(EventType::Signal as u8, timeout);
        let copy_status = copy_from_kernel(&mut buffer).unwrap();

        check_eq!(status, Status::Ok);
        check_eq!(copy_status, Status::Ok);

        let received_signal = u32::from_ne_bytes(event.data);

        log_line!(
            USER_AUTOTEST_INFO,
            "{:?}:{}:{:#x}:src={:#x} signal={}",
            event.header.event,
            event.header.length,
            event.header.magic,
            event.header.peer,
            received_signal
        );

        check_eq!(received_signal, sig as u32);
    }

    test_end!();
}


pub fn run() {
    test_suite_start!("syscall::signal");
    test_signal_sendrecv();
    test_suite_end!("syscall::signal");
}
