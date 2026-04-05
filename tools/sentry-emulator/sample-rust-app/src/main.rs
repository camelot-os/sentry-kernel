// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0


fn main() {
    fn daemon_log(msg: &str) {
        let _ = sentry_uapi::copy_to_kernel(&msg.as_bytes());
        let _ = sentry_uapi::syscall::log(msg.len());
    }

    let my_label = std::env::var("SENTRY_APP_LABEL")
        .ok()
        .and_then(|raw| raw.parse::<u32>().ok())
        .unwrap_or(7);

    daemon_log("[1] get_process_handle(self)");
    let st_proc = sentry_uapi::syscall::get_process_handle(my_label);
    let mut my_handle: u32 = 0;
    let _ = sentry_uapi::copy_from_kernel(&mut my_handle);
    daemon_log(&format!("status={st_proc:?} handle={my_handle}"));

    let peer_label = if my_label == 7 { 8 } else { 7 };
    daemon_log("[2] get_process_handle(peer) + send_signal(peer_handle, SIGUSR1)");
    let st_peer = sentry_uapi::syscall::get_process_handle(peer_label);
    let mut peer_handle: u32 = 0;
    let _ = sentry_uapi::copy_from_kernel(&mut peer_handle);
    daemon_log(&format!("peer_lookup status={st_peer:?} handle={peer_handle}"));
    if st_peer == sentry_uapi::systypes::Status::Ok {
        let st_sig_peer = sentry_uapi::syscall::send_signal(peer_handle, sentry_uapi::systypes::Signal::Usr1);
        daemon_log(&format!("send_signal status={st_sig_peer:?}"));
    }

    daemon_log("[3] alarm(start then stop)");
    let st_alarm_start = sentry_uapi::syscall::alarm(50, sentry_uapi::systypes::AlarmFlag::AlarmStartPeriodic);
    let st_alarm_stop = sentry_uapi::syscall::alarm(50, sentry_uapi::systypes::AlarmFlag::AlarmStop);
    daemon_log(&format!("start={st_alarm_start:?} stop={st_alarm_stop:?}"));

    daemon_log("[4] get_random");
    let st_rng = sentry_uapi::syscall::get_random();
    let mut rng_value: u32 = 0;
    let _ = sentry_uapi::copy_from_kernel(&mut rng_value);
    daemon_log(&format!("status={st_rng:?} value={rng_value}"));

    daemon_log("[5] get_cycle(Milliseconds)");
    let st_cycle = sentry_uapi::syscall::get_cycle(sentry_uapi::systypes::Precision::Milliseconds);
    let mut cycle_value: u64 = 0;
    let _ = sentry_uapi::copy_from_kernel(&mut cycle_value);
    daemon_log(&format!("status={st_cycle:?} value={cycle_value}"));
}
