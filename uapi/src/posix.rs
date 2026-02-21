// Copyright 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

///
/// This module provides a POSIX-compatible implementation of the Sentry kernel
/// interface for Linux/x86_64 targets.
/// It serves as a compatibility layer, allowing applications to behave as if
/// they were interacting with the Sentry kernel, but  using standard
/// POSIX system calls and conventions.
/// This implementation is intended for use in environments where the Sentry kernel
/// is not available, such as during development or testing on a standard Linux system.
///
/// In order to support multi-tasking and inter-process communication (IPC) in a POSIX environment,
/// this module will interact with a local GNU/Linux server that simulates the Sentry kernel's behavior.
/// This server will handle the necessary system calls and manage the state of the simulated kernel,
/// allowing applications to communicate with external objects such as devices, shared memory,
/// and other task.
/// This server will be written as a separate component in this repository, in the tools directory.
/// Interactions with this server will be made through a local socket, and the protocol will be defined
/// in the documentation of the server itself, as well as in the documentation of this module.
///
/// Each Except for local-only syscalls such as `sched_yield` or `sys_exit`, all the syscalls
/// will behave as a proxy to the server, forwarding the syscall number and arguments to the
/// server and returning the server's response as the syscall result.
///

use crate::systypes::*;


#[inline(always)]
pub fn exit(status: i32) -> Status {
    std::process::exit(status);
}

#[inline(always)]
pub fn sleep(_duration_ms: SleepDuration, _mode: SleepMode) -> Status {
    todo!("Convert local sleep API to std::thread::sleep");
}

#[inline(always)]
pub fn sched_yield() -> Status {
    std::thread::yield_now();
    Status::Ok
}

#[inline(always)]
pub fn get_process_handle(_label: TaskLabel) -> Status {
    // Pas d'équivalent POSIX direct
    todo!("get_process_handle not implemented in POSIX mode");
}
#[inline(always)]
pub fn get_current_process() -> Status {
    // POSIX: getpid()
    let _pid = std::process::id();
    Status::Ok
}
// -------------------------------------------------------------------------
// IPC / Events
// -------------------------------------------------------------------------
#[inline(always)]
pub fn send_ipc(_target: TaskHandle, _length: u8) -> Status {
    todo!("send_ipc not implemented in POSIX mode");
}
#[inline(always)]
pub fn wait_for_event(_mask: u8, _timeout: i32) -> Status {
    todo!("wait_for_event not implemented in POSIX mode");
}

#[inline(always)]
pub fn map_dev(_handle: DeviceHandle) -> Status {
    todo!("map_dev not implemented in POSIX mode");
}

#[inline(always)]
pub fn unmap_dev(_handle: DeviceHandle) -> Status {
    todo!("map_dev not implemented in POSIX mode");
}

#[inline(always)]
pub fn get_shm_handle(_shm: ShmLabel) -> Status {
    todo!("get_shm_handle not implemented in POSIX mode");
}

#[inline(always)]
pub fn get_device_handle(_devlabel: u8) -> Status {
    todo!("get_device_handle not implemented in POSIX mode");
}

#[inline(always)]
pub fn get_dma_stream_handle(_stream: StreamLabel) -> Status {
    todo!("get_dma_stream_handle not implemented in POSIX mode");
}

#[inline(always)]
pub fn start(_process: TaskLabel) -> Status {
    todo!("start not implemented in POSIX mode");
}

#[inline(always)]
pub fn map_shm(_shm: ShmHandle) -> Status {
    todo!("map_shm not implemented in POSIX mode");
}

#[inline(always)]
pub fn unmap_shm(_shm: ShmHandle) -> Status {
    todo!("unmap_shm not implemented in POSIX mode");
}

#[inline(always)]
pub fn shm_set_credential(
    _shm: ShmHandle,
    _id: TaskHandle,
    _shm_perm: u32,
) -> Status {
    todo!("shm_set_credential not implemented in POSIX mode");
}

#[inline(always)]
pub fn send_signal(_target: u32, _sig: Signal) -> Status {
    todo!("send_signal not implemented in POSIX mode");
}

#[inline(always)]
pub fn gpio_get(_resource: u32, _io: u8) -> Status {
    todo!("gpio_get not implemented in POSIX mode");
}

#[inline(always)]
pub fn gpio_set(_resource: u32, _io: u8, _val: bool) -> Status {
    todo!("gpio_set not implemented in POSIX mode");
}

#[inline(always)]
pub fn gpio_reset(_resource: u32, _io: u8) -> Status {
    todo!("gpio_reset not implemented in POSIX mode");
}

#[inline(always)]
pub fn gpio_toggle(_resource: u32, _io: u8) -> Status {
    todo!("gpio_toggle not implemented in POSIX mode");
}

#[inline(always)]
pub fn gpio_configure(_resource: u32, _io: u8) -> Status {
    todo!("gpio_configure not implemented in POSIX mode");
}

#[inline(always)]
pub fn irq_acknowledge(_irq: u16) -> Status {
    todo!("irq_acknowledge not implemented in POSIX mode");
}

#[inline(always)]
pub fn irq_enable(_irq: u16) -> Status {
    todo!("irq_enable not implemented in POSIX mode");
}

#[inline(always)]
pub fn irq_disable(_irq: u16) -> Status {
    todo!("irq_disable not implemented in POSIX mode");
}

#[inline(always)]
pub fn pm_manage(_mode: CPUSleep) -> Status {
    todo!("pm_manage not implemented in POSIX mode");
}

#[inline(always)]
pub fn alarm(_timeout_ms: u32, _flag: AlarmFlag) -> Status {
    todo!("alarm not implemented in POSIX mode");
}

#[inline(always)]
pub fn log(_length: usize) -> Status {
    todo!("log not implemented in POSIX mode");
}

#[inline(always)]
pub fn get_random() -> Status {
    todo!("get_random not implemented in POSIX mode");
}

#[inline(always)]
pub fn get_cycle(_precision: Precision) -> Status {
    todo!("get_cycle not implemented in POSIX mode");
}

#[inline(always)]
pub fn pm_set_clock(_clk_reg: u32, _clkmsk: u32, _val: u32) -> Status {
    todo!("pm_set_clock not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_start_stream(_dmah: StreamHandle) -> Status {
    todo!("dma_start_stream not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_suspend_stream(_dmah: StreamHandle) -> Status {
    todo!("dma_suspend_stream not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_get_stream_status(_dmah: StreamHandle) -> Status {
    todo!("dma_get_stream_status not implemented in POSIX mode");
}

#[inline(always)]
pub fn shm_get_infos(_shm: ShmHandle) -> Status {
    todo!("shm_get_infos not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_assign_stream(_dmah: StreamHandle) -> Status {
    todo!("dma_assign_stream not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_unassign_stream(_dmah: StreamHandle) -> Status {
    todo!("dma_unassign_stream not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_get_stream_info(_dmah: StreamHandle) -> Status {
    todo!("dma_get_stream_info not implemented in POSIX mode");
}

#[inline(always)]
pub fn dma_resume_stream(_dmah: StreamHandle) -> Status {
    todo!("dma_resume_stream not implemented in POSIX mode");
}

// Autotest only
#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[inline(always)]
pub fn autotest_set_capa(_capa: u32) -> Status {
    todo!("autotest_set_capa not implemented in POSIX mode");
}

#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[inline(always)]
pub fn autotest_clear_capa(_capa: u32) -> Status {
    todo!("autotest_clear_capa not implemented in POSIX mode");
}

// -------------------------------------------------------------------------
// Default fallback helper
// -------------------------------------------------------------------------
#[inline(always)]
pub fn unsupported() -> Status {
    todo!("Unsupported syscall in POSIX GNU/Linux mode");
}
