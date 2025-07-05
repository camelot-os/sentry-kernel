// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check;
use crate::check_eq;
use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use core::prelude::v1::Ok;
use sentry_uapi::syscall::dma_assign_stream;
use sentry_uapi::syscall::dma_get_stream_info;
use sentry_uapi::syscall::dma_get_stream_status;
use sentry_uapi::syscall::dma_start_stream;
use sentry_uapi::syscall::dma_suspend_stream;
use sentry_uapi::syscall::dma_unassign_stream;
use sentry_uapi::syscall::get_dma_stream_handle;
use sentry_uapi::syscall::get_process_handle;
use sentry_uapi::syscall::get_shm_handle;
use sentry_uapi::syscall::map_shm;
use sentry_uapi::syscall::shm_get_infos;
use sentry_uapi::syscall::shm_set_credential;
use sentry_uapi::syscall::wait_for_event;
use sentry_uapi::systypes::EventType;
use sentry_uapi::systypes::SHMPermission;
use sentry_uapi::systypes::ShmHandle;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::StreamHandle;
use sentry_uapi::systypes::TaskHandle;
use sentry_uapi::systypes::dma::*;
use sentry_uapi::systypes::shm::ShmInfo;
use sentry_uapi::*;

#[unsafe(no_mangle)]
pub extern "C" fn test_dma() -> bool {
    let mut all_ok = true;
    test_suite_start!("sys_dma");

    all_ok &= test_dma_get_handle_inval();
    all_ok &= test_dma_manipulate_stream_badhandle();
    all_ok &= test_dma_assign_unassign_stream();
    all_ok &= test_dma_start_stream();
    all_ok &= test_dma_get_stream_status();
    all_ok &= test_dma_stop_stream();
    all_ok &= test_dma_start_n_wait_stream();
    all_ok &= test_dma_get_info();

    test_suite_end!("sys_dma");
    all_ok
}

fn test_dma_get_handle_inval() -> bool {
    test_start!();
    let ok = check_eq!(get_dma_stream_handle(0x42), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_manipulate_stream_badhandle() -> bool {
    test_start!();
    let ok = check_eq!(dma_start_stream(0), Status::Invalid)
        & check_eq!(dma_suspend_stream(0), Status::Invalid)
        & check_eq!(dma_get_stream_status(0), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_assign_unassign_stream() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let ok = check_eq!(get_dma_stream_handle(0x2), Status::Ok)
        & (copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok))
        & check_eq!(dma_assign_stream(streamh), Status::Ok)
        & check_eq!(dma_assign_stream(streamh), Status::Invalid)
        & check_eq!(dma_unassign_stream(streamh), Status::Ok)
        & check_eq!(dma_unassign_stream(streamh), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_start_stream() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let ok = check_eq!(get_dma_stream_handle(0x2), Status::Ok)
        & (copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok))
        & check_eq!(dma_start_stream(streamh), Status::Invalid)
        & check_eq!(dma_assign_stream(streamh), Status::Ok)
        & check_eq!(dma_start_stream(streamh), Status::Ok)
        & check_eq!(dma_assign_stream(streamh), Status::Invalid)
        & check_eq!(dma_start_stream(streamh), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_get_stream_status() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let ok = check_eq!(get_dma_stream_handle(0x2), Status::Ok)
        & (copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok))
        & check_eq!(dma_get_stream_status(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_stop_stream() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let ok = check_eq!(get_dma_stream_handle(0x2), Status::Ok)
        & (copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok))
        & check_eq!(dma_suspend_stream(streamh), Status::Ok)
        & check_eq!(dma_unassign_stream(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_start_n_wait_stream() -> bool {
    test_start!();
    let mut ok = true;
    let mut streamh: StreamHandle = 0;
    ok &= check_eq!(get_dma_stream_handle(0x2), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok);

    let mut myself: TaskHandle = 0;
    ok &= check_eq!(get_process_handle(0xbabe), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut myself as *mut _ as *mut u8)) == Ok(Status::Ok);

    let mut shm1: ShmHandle = 0;
    let mut info1 = ShmInfo {
        label: 0 as u32,
        handle: 0 as u32,
        base: 0 as usize,
        len: 0 as usize,
        perms: 0 as u32,
    };
    ok &= check_eq!(get_shm_handle(shm1), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut shm1 as *mut _ as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(
        shm_set_credential(
            shm1,
            myself,
            SHMPermission::Write as u32 | SHMPermission::Map as u32
        ),
        Status::Ok
    );
    ok &= check_eq!(map_shm(shm1), Status::Ok);
    ok &= check_eq!(shm_get_infos(shm1), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut info1 as *mut _ as *mut u8)) == Ok(Status::Ok);
    unsafe {
        core::ptr::write_bytes(info1.base as *mut u8, 0xa5, 0x100);
    }

    let mut shm2: ShmHandle = 0;
    let mut info2 = ShmInfo {
        label: 0 as u32,
        handle: 0 as u32,
        base: 0 as usize,
        len: 0 as usize,
        perms: 0 as u32,
    };
    ok &= check_eq!(get_shm_handle(shm2), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut shm2 as *mut _ as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(
        shm_set_credential(
            shm2,
            myself,
            SHMPermission::Write as u32 | SHMPermission::Map as u32
        ),
        Status::Ok
    );
    ok &= check_eq!(map_shm(shm2), Status::Ok);
    ok &= check_eq!(shm_get_infos(shm2), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut info2 as *mut _ as *mut u8)) == Ok(Status::Ok);
    unsafe {
        core::ptr::write_bytes(info2.base as *mut u8, 0x42, 0x100);
    }

    ok &= check_eq!(dma_assign_stream(streamh), Status::Ok);
    ok &= check_eq!(dma_start_stream(streamh), Status::Ok);
    ok &= check_eq!(wait_for_event(EventType::Dma as u8, -1), Status::Ok);

    let cmp = unsafe {
        core::slice::from_raw_parts(info1.base as *const u8, 0x100)
            == core::slice::from_raw_parts(info2.base as *const u8, 0x100)
    };
    ok &= check!(cmp, "SHM1 == SHM2 after DMA copy");

    ok &= check_eq!(dma_suspend_stream(streamh), Status::Ok);
    ok &= check_eq!(dma_unassign_stream(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_get_info() -> bool {
    test_start!();
    let mut ok = true;
    let mut streamh: StreamHandle = 0;
    let mut stream_info = GpdmaStreamConfig {
        channel: 0 as u16,
        stream: 0 as u16,
        controller: 0 as u16,
        transfer_type: 0 as u16,
        source: 0 as usize,
        dest: 0 as usize,
        transfer_len: 0 as usize,
        circular_source: false,
        circular_dest: false,
        interrupts: 0 as u8,
        is_triggered: false,
        trigger: 0 as u8,
        priority: 0 as u8,
        transfer_mode: 0 as u8,
        src_beat_len: 0 as u8,
        dest_beat_len: 0 as u8,
    };
    let mut shm: ShmHandle = 0;
    let mut infos = ShmInfo {
        label: 0 as u32,
        handle: 0 as u32,
        base: 0 as usize,
        len: 0 as usize,
        perms: 0 as u32,
    };

    ok &= check_eq!(get_shm_handle(shm), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(shm_get_infos(shm), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut infos as *mut _ as *mut u8)) == Ok(Status::Ok);

    ok &= check_eq!(get_dma_stream_handle(0x1), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok);

    ok &= check_eq!(dma_get_stream_info(streamh), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut stream_info as *mut _ as *mut u8)) == Ok(Status::Ok);

    ok &= check_eq!(stream_info.stream, 112);
    ok &= check_eq!(stream_info.channel, 1);
    ok &= check_eq!(stream_info.controller, 0);
    ok &= check_eq!(
        stream_info.transfer_type as u32,
        GpdmaTransferType::DeviceToMemory as u32
    );
    ok &= check_eq!(stream_info.transfer_len, 42);
    ok &= check_eq!(stream_info.source, 0);
    ok &= check_eq!(stream_info.dest, infos.base);
    ok &= check_eq!(stream_info.circular_source, false);
    ok &= check_eq!(stream_info.circular_dest, true);
    ok &= check_eq!(stream_info.priority as u32, GpdmaPriority::Medium as u32);
    test_end!();
    ok
}
