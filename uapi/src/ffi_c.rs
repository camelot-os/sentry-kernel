// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 ANSSI & H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

use crate::exchange;
use crate::systypes::*;

/// C interface to [`crate::syscall::get_process_handle`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_get_process_handle(process: TaskLabel) -> Status {
    crate::syscall::get_process_handle(process)
}

/// C interface to [`crate::syscall::exit`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_exit(status: i32) -> Status {
    crate::syscall::exit(status)
}

/// C interface to [`crate::syscall::get_shm_handle`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_get_shm_handle(shm: ShmLabel) -> Status {
    crate::syscall::get_shm_handle(shm)
}

/// C interface to [`crate::syscall::get_dma_stream_handle`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_get_dma_stream_handle(stream: StreamLabel) -> Status {
    crate::syscall::get_dma_stream_handle(stream)
}

/// C interface to [`crate::syscall::sched_yield`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_sched_yield() -> Status {
    crate::syscall::sched_yield()
}

/// C interface to [`crate::syscall::sleep`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_sleep(duration_ms: SleepDuration, mode: SleepMode) -> Status {
    crate::syscall::sleep(duration_ms, mode)
}

/// C interface to [`crate::syscall::start`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_start(process: TaskLabel) -> Status {
    crate::syscall::start(process)
}

/// C interface to [`crate::syscall::map_dev`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_map_dev(dev: DeviceHandle) -> Status {
    crate::syscall::map_dev(dev as DeviceHandle)
}

/// C interface to [`crate::syscall::map_shm`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_map_shm(shm: ShmHandle) -> Status {
    crate::syscall::map_shm(shm as ShmHandle)
}

/// C interface to [`crate::syscall::unmap_dev`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_unmap_dev(dev: DeviceHandle) -> Status {
    crate::syscall::unmap_dev(dev as DeviceHandle)
}

/// C interface to [`crate::syscall::unmap_shm`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_unmap_shm(shm: ShmHandle) -> Status {
    crate::syscall::unmap_shm(shm as ShmHandle)
}

/// C interface to [`crate::syscall::shm_set_credential`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_shm_set_credential(
    shm: ShmHandle,
    id: TaskHandle,
    shm_perm: u32,
) -> Status {
    crate::syscall::shm_set_credential(shm, id, shm_perm)
}

/// C interface to [`crate::syscall::send_ipc`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_send_ipc(target: TaskHandle, length: u8) -> Status {
    crate::syscall::send_ipc(target, length)
}

/// C interface to [`crate::syscall::send_signal`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_send_signal(resource: u32, signal_type: Signal) -> Status {
    crate::syscall::send_signal(resource, signal_type)
}

/// C interface to [`crate::syscall::gpio_get`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_gpio_get(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_get(resource, io)
}

/// C interface to [`crate::syscall::gpio_set`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_gpio_set(resource: u32, io: u8, val: bool) -> Status {
    crate::syscall::gpio_set(resource, io, val)
}

/// C interface to [`crate::syscall::gpio_reset`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_gpio_reset(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_reset(resource, io)
}

/// C interface to [`crate::syscall::gpio_toggle`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_gpio_toggle(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_toggle(resource, io)
}

/// C interface to [`crate::syscall::gpio_configure`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_gpio_configure(resource: u32, io: u8) -> Status {
    crate::syscall::gpio_configure(resource, io)
}

/// C interface to [`crate::syscall::get_device_handle`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_get_device_handle(devlabel: u8) -> Status {
    crate::syscall::get_device_handle(devlabel)
}

/// C interface to [`crate::syscall::irq_acknowledge`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_irq_acknowledge(irq: u16) -> Status {
    crate::syscall::irq_acknowledge(irq)
}

/// C interface to [`crate::syscall::irq_enable`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_irq_enable(irq: u16) -> Status {
    crate::syscall::irq_enable(irq)
}

/// C interface to [`crate::syscall::irq_disable`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_irq_disable(irq: u16) -> Status {
    crate::syscall::irq_disable(irq)
}

/// C interface to [`crate::syscall::wait_for_event`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_wait_for_event(mask: u8, timeout: i32) -> Status {
    crate::syscall::wait_for_event(mask, timeout)
}

/// C interface to [`crate::syscall::pm_manage`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_pm_manage(mode: CPUSleep) -> Status {
    crate::syscall::pm_manage(mode)
}

/// C interface to [`crate::syscall::alarm`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_alarm(timeout_ms: u32, flag: AlarmFlag) -> Status {
    crate::syscall::alarm(timeout_ms, flag)
}

/// C interface to [`crate::syscall::log`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_log(length: usize) -> Status {
    crate::syscall::log(length)
}

/// C interface to [`crate::syscall::get_random`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_get_random() -> Status {
    crate::syscall::get_random()
}

/// C interface to [`crate::syscall::get_cycle`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_get_cycle(precision: Precision) -> Status {
    crate::syscall::get_cycle(precision)
}

/// C interface to [`crate::syscall::pm_set_clock`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_pm_set_clock(clk_reg: u32, clkmsk: u32, val: u32) -> Status {
    crate::syscall::pm_set_clock(clk_reg, clkmsk, val)
}

/// C interface to [`crate::syscall::dma_start_stream`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_start_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_start_stream(dmah)
}

/// C interface to [`crate::syscall::dma_suspend_stream`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_suspend_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_suspend_stream(dmah)
}

/// C interface to [`crate::syscall::dma_get_stream_status`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_get_stream_status(dmah: StreamHandle) -> Status {
    crate::syscall::dma_get_stream_status(dmah)
}

/// C interface to [`crate::syscall::shm_get_infos`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_shm_get_infos(shm: ShmHandle) -> Status {
    crate::syscall::shm_get_infos(shm)
}

/// C interface to [`crate::syscall::dma_assign_stream`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_assign_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_assign_stream(dmah)
}

/// C interface to [`crate::syscall::dma_unassign_stream`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_unassign_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_unassign_stream(dmah)
}

/// C interface to [`crate::syscall::dma_get_stream_info`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_get_stream_info(dmah: StreamHandle) -> Status {
    crate::syscall::dma_get_stream_info(dmah)
}

/// C interface to [`crate::syscall::dma_resume_stream`] syscall Rust implementation
#[unsafe(no_mangle)]
pub extern "C" fn __sys_dma_resume_stream(dmah: StreamHandle) -> Status {
    crate::syscall::dma_resume_stream(dmah)
}

/// C interface to [`crate::syscall::autotest_set_capa`] syscall Rust implementation
#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[unsafe(no_mangle)]
pub extern "C" fn __sys_autotest_set_capa(capa: u32) -> Status {
    crate::syscall::autotest_set_capa(capa)
}

/// C interface to [`crate::syscall::autotest_clear_capa`] syscall Rust implementation
#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[unsafe(no_mangle)]
pub extern "C" fn __sys_autotest_clear_capa(capa: u32) -> Status {
    crate::syscall::autotest_clear_capa(capa)
}

/// # Safety
/// Conditions for code::slice::from_raw_parts are not violated
/// C interface to [`crate::copy_to_kernel`] Rust implementation
#[unsafe(no_mangle)]
pub unsafe extern "C" fn copy_to_kernel(from: *mut u8, length: usize) -> Status {
    let u8_slice: &[u8] = unsafe { core::slice::from_raw_parts(from, length) };
    match exchange::copy_to_kernel(&u8_slice) {
        Ok(_) => Status::Ok,
        Err(err) => err,
    }
}

/// # Safety
/// Conditions for code::slice::from_raw_parts are not violated
/// C interface to [`crate::copy_from_kernel`] Rust implementation
#[unsafe(no_mangle)]
pub unsafe extern "C" fn copy_from_kernel(to: *mut u8, length: usize) -> Status {
    let mut u8_slice: &mut [u8] =
        unsafe { core::slice::from_raw_parts_mut(to, length) as &mut [u8] };
    match exchange::copy_from_kernel(&mut u8_slice) {
        Ok(_) => Status::Ok,
        Err(err) => err,
    }
}
