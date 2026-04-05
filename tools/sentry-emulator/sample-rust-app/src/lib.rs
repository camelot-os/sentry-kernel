// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

//! Sample Rust tasks used to validate the sentry-emulator end-to-end behavior.
//!
//! `sample-app-one` actively sends a signal to `sample-app-two`, then runs alarm,
//! random, and cycle syscalls. `sample-app-two` blocks on event delivery, decodes
//! the serialized signal event from exchange memory, and runs the same checks.

use sentry_uapi::systypes::{
    AlarmFlag, EventType, Precision, Signal, Status,
};
use std::thread;
use std::time::Duration;

/// Copy a UTF-8 log message into exchange memory and emit it with `syscall::log`.
fn emit_app_log(message: &str) {
    let payload = message.as_bytes();
    let st_copy = sentry_uapi::copy_to_kernel(&payload).unwrap_or(Status::Invalid);
    if st_copy != Status::Ok {
        eprintln!("[sample-rust-app][fallback] copy_to_kernel(log) failed: {st_copy:?}");
        return;
    }

    let st_log = sentry_uapi::syscall::log(payload.len());
    if st_log != Status::Ok {
        eprintln!("[sample-rust-app][fallback] syscall::log failed: {st_log:?}");
    }
}

/// Emit a structured status line for one syscall step.
fn report_status(context: &str, status: Status) {
    emit_app_log(&format!("{context}: {status:?}"));
}

const SIGNAL_EVENT_TYPE: u8 = 2;
const SIGNAL_EVENT_MAGIC: u16 = 0x4242;
const TARGET_APP_TWO_HANDLE: u32 = 2;

/// Decode a signal event header and payload from exchange memory.
///
/// Returns `Some(signal)` when the buffer contains a valid serialized signal
/// event, otherwise returns `None` and logs the invalid frame details.
fn read_signal_event_from_exchange() -> Option<u32> {
    let mut raw_exchange = [0u8; 128];
    let mut raw_exchange_slice: &mut [u8] = &mut raw_exchange;
    let st_copy_event =
        sentry_uapi::copy_from_kernel(&mut raw_exchange_slice).unwrap_or(Status::Invalid);
    report_status("copy_from_kernel(raw signal event)", st_copy_event);
    if st_copy_event != Status::Ok {
        return None;
    }

    let event_type = raw_exchange[0];
    let event_len = raw_exchange[1];
    let event_magic = u16::from_le_bytes([raw_exchange[2], raw_exchange[3]]);
    let event_peer = u32::from_le_bytes([
        raw_exchange[4],
        raw_exchange[5],
        raw_exchange[6],
        raw_exchange[7],
    ]);
    let signal = u32::from_le_bytes([
        raw_exchange[8],
        raw_exchange[9],
        raw_exchange[10],
        raw_exchange[11],
    ]);

    if event_type != SIGNAL_EVENT_TYPE
        || event_len != 4
        || event_magic != SIGNAL_EVENT_MAGIC
        || event_peer == 0
    {
        emit_app_log(&format!(
            "invalid signal event header: type={event_type} len={event_len} magic=0x{event_magic:04x} peer={event_peer}"
        ));
        return None;
    }

    emit_app_log(&format!(
        "signal event received from peer={event_peer} value={signal}"
    ));
    Some(signal)
}

/// Exercise alarm, random, and cycle syscalls and log each returned status.
fn run_alarm_random_cycle_checks() {
    // Start periodic alarm to guarantee that an immediate stop targets a live registration.
    let st_alarm_start = sentry_uapi::syscall::alarm(5000, AlarmFlag::AlarmStartPeriodic);
    let st_alarm_stop = sentry_uapi::syscall::alarm(5000, AlarmFlag::AlarmStop);
    report_status("alarm(start)", st_alarm_start);
    if st_alarm_stop == Status::NoEntity {
        emit_app_log("alarm(stop): Ok (already stopped)");
    } else {
        report_status("alarm(stop)", st_alarm_stop);
    }

    let st_rng = sentry_uapi::syscall::get_random();
    let mut rng_value: u32 = 0;
    let st_copy_rng = sentry_uapi::copy_from_kernel(&mut rng_value).unwrap_or(Status::Invalid);
    report_status("get_random", st_rng);
    report_status("copy_from_kernel(random)", st_copy_rng);

    let st_cycle = sentry_uapi::syscall::get_cycle(Precision::Milliseconds);
    let mut cycle_value: u64 = 0;
    let st_copy_cycle =
        sentry_uapi::copy_from_kernel(&mut cycle_value).unwrap_or(Status::Invalid);
    report_status("get_cycle", st_cycle);
    report_status("copy_from_kernel(cycle)", st_copy_cycle);
}

/// Entry routine for sample app one.
///
/// The routine sends `SIGUSR1` to app two twice (to tolerate startup ordering),
/// then validates additional emulator syscalls.
pub fn run_sample_app_one(peer_label: u32) {
    let _ = peer_label;

    // Let the receiver enter its blocking wait path before sending the signal.
    thread::sleep(Duration::from_millis(100));

    let st_sig_peer = sentry_uapi::syscall::send_signal(TARGET_APP_TWO_HANDLE, Signal::Usr1);
    report_status("send_signal(peer, SIGUSR1)", st_sig_peer);

    // Emit a second signal to make the emulator e2e startup phase robust against transient ordering.
    let st_sig_peer_retry = sentry_uapi::syscall::send_signal(TARGET_APP_TWO_HANDLE, Signal::Usr1);
    report_status("send_signal(peer, SIGUSR1, retry)", st_sig_peer_retry);
    run_alarm_random_cycle_checks();
}

/// Entry routine for sample app two.
///
/// The routine blocks on signal events until `SIGUSR1` is received, validates
/// signal event serialization, then runs the shared syscall checks.
pub fn run_sample_app_two() {
    // Wait without timeout and return only when SIGUSR1 has been serialized by daemon.
    loop {
        let st_wait_signal = sentry_uapi::syscall::wait_for_event(EventType::Signal.into(), 0);
        if st_wait_signal != Status::Ok {
            report_status("wait_for_event(signal, no timeout)", st_wait_signal);
            continue;
        }
        let Some(signal) = read_signal_event_from_exchange() else {
            continue;
        };

        report_status("wait_for_event(signal, no timeout)", st_wait_signal);

        if signal == Signal::Usr1 as u32 {
            break;
        }

        emit_app_log(&format!("ignoring other signal value={signal}"));
    }
    run_alarm_random_cycle_checks();
}
