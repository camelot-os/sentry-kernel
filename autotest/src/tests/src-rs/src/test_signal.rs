// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use sentry_uapi::status::Status;
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

    let ret = unsafe { __sys_get_process_handle(0xbabe) };
    if ret != Status::Ok {
        log_info!("get_process_handle failed: {:?}", ret);
        test_end!();
        return false;
    }

    if unsafe {
        copy_from_kernel(
            &mut handle as *mut _ as *mut u8,
            core::mem::size_of::<TaskHandle>(),
        )
    } != Status::Ok
    {
        log_info!("copy_from_kernel(handle) failed");
        test_end!();
        return false;
    }

    log_info!("handle is {:#x}", handle);
    for sig_val in (Signal::Abort as u32)..=(Signal::Usr2 as u32) {
        let sig = unsafe { core::mem::transmute::<u32, Signal>(sig_val) };
        log_info!("sending signal {:?} to myself", sig);

        let ret_send = unsafe { __sys_send_signal(handle, sig) };
        let ret_wait = unsafe { __sys_wait_for_event(EventType::Signal as u8, timeout) };

        let copy_status = unsafe {
            copy_from_kernel(
                buffer.as_mut_ptr(),
                core::mem::size_of::<ExchangeEvent>() + 4,
            )
        };

        if ret_send != Status::Ok || ret_wait != Status::Ok || copy_status != Status::Ok {
            log_info!(
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

        log_info!(
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
