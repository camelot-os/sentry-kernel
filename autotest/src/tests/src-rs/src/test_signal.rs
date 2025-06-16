// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::test_log::USER_AUTOTEST_INFO;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use sentry_uapi::syscall::get_process_handle;
use sentry_uapi::syscall::send_signal;
use sentry_uapi::syscall::wait_for_event;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::*;
use sentry_uapi::*;

#[repr(C)]
#[derive(Copy, Clone)]
struct ExchangeEvent {
    header: ExchangeHeader,
    data: [u8; 64],
}


fn test_signal_sendrecv() -> bool {
    test_start!();

    let mut ok = true;
    let mut handle: TaskHandle = 0;
    let timeout: i32 = 20;
    let mut buffer = [0u8; core::mem::size_of::<ExchangeEvent>() + 4];

    let ret = get_process_handle(0xbabe);
    if ret != Status::Ok {
        log_line!(USER_AUTOTEST_INFO, "get_process_handle failed: {:?}", ret);
        test_end!();
        return false;
    }

    if unsafe { copy_from_kernel(&mut (&mut handle as *mut _ as *mut u8)) } != Ok(Status::Ok) {
        log_line!(USER_AUTOTEST_INFO, "copy_from_kernel(handle) failed");
        test_end!();
        return false;
    }

    log_line!(USER_AUTOTEST_INFO, "handle is {:#x}", handle);
    for sig_val in (Signal::Abort as u32)..=(Signal::Usr2 as u32) {
        let sig = unsafe { core::mem::transmute::<u32, Signal>(sig_val) };
        log_line!(USER_AUTOTEST_INFO, "sending signal {:?} to myself", sig);

        let ret_send = unsafe { send_signal(handle, sig) };
        let ret_wait = unsafe { wait_for_event(EventType::Signal as u8, timeout) };

        let copy_status = unsafe { copy_from_kernel(&mut buffer.as_mut_ptr()) };

        if ret_send != Status::Ok || ret_wait != Status::Ok || copy_status != Ok(Status::Ok) {
            log_line!(
                USER_AUTOTEST_INFO,
                "signal {:?} failed: send={:?}, wait={:?}, copy={:?}",
                sig,
                ret_send,
                ret_wait,
                copy_status
            );
            ok = false;
            continue;
        }

        let event = unsafe { &*(buffer[4..].as_ptr() as *const ExchangeEvent) };
        let received_signal = u32::from_ne_bytes(event.data[0..4].try_into().unwrap_or([0; 4]));

        log_line!(
            USER_AUTOTEST_INFO,
            "{:?}:{}:{:#x}:src={:#x} signal={}",
            event.header.event,
            event.header.length,
            event.header.magic,
            event.header.peer,
            received_signal
        );

        ok &= check_eq!(received_signal, sig as u32);
    }

    test_end!();
    ok
}
pub fn test_signal() -> bool {
    test_suite_start!("sys_signal");
    let mut ok = true;

    ok &= test_signal_sendrecv();

    test_suite_end!("sys_signal");
    ok
}
