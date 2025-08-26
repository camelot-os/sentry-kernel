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
use sentry_uapi::systypes::EventType;
use sentry_uapi::systypes::SHMPermission;
use sentry_uapi::systypes::ShmHandle;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::StreamHandle;
use sentry_uapi::systypes::TaskHandle;
use sentry_uapi::systypes::dma::*;
use sentry_uapi::systypes::shm::ShmInfo;
use sentry_uapi::*;
use crate::tests::devices_utils::get_shm_by_name;

pub fn run() -> bool {
    test_suite_start!("syscall::dma*");
    let mut ok = true;

    ok &= test_dma_get_handle_inval();
    ok &= test_dma_get_info();
    ok &= test_dma_manipulate_stream_badhandle();
    ok &= test_dma_assign_unassign_stream();
    ok &= test_dma_start_n_wait_stream();
    ok &= test_dma_start_stream();
    ok &= test_dma_get_stream_status();

    test_suite_end!("syscall::dma*");
    ok
}

fn test_dma_get_handle_inval() -> bool {
    test_start!();
    let ok = check_eq!(syscall::get_dma_stream_handle(0x42), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_manipulate_stream_badhandle() -> bool {
    test_start!();
    let mut status : systypes::Status;
    let mut ok = true;
    status = syscall::dma_start_stream(0);
    ok &= check_eq!(status, systypes::Status::Invalid);

    status = syscall::dma_suspend_stream(0);
    ok &= check_eq!(status, systypes::Status::Invalid);

    status = syscall::dma_get_stream_status(0);
    ok &= check_eq!(status, systypes::Status::Invalid);
    test_end!();
    ok
}

fn test_dma_assign_unassign_stream() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let mut status = syscall::get_dma_stream_handle(0x2);
    let mut ok = true;
    let _ = copy_from_kernel(&mut streamh);
    check_eq!(status, Status::Ok);

    status = syscall::dma_assign_stream(streamh);
    ok &= check_eq!(status, Status::Ok);
    status = syscall::dma_assign_stream(streamh);
    ok &= check_eq!(status, Status::Invalid);

    status = syscall::dma_unassign_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::dma_unassign_stream(streamh);
    ok &= check_eq!(status, Status::Invalid);

    test_end!();
    ok
}

fn test_dma_start_stream() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let mut ok = true;

    let mut status = syscall::get_dma_stream_handle(0x2);
    let _ = copy_from_kernel(&mut streamh);
    check_eq!(status, Status::Ok);

    status = syscall::dma_start_stream(streamh);
    check_eq!(status, Status::Invalid);

    status = syscall::dma_assign_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::dma_start_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::dma_assign_stream(streamh);
    ok &= check_eq!(status, Status::Invalid);

    status = syscall::dma_start_stream(streamh);
    ok &= check_eq!(status, Status::Invalid);

    // avoiding border effects, stop & unassign the stream
    status = syscall::dma_suspend_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::dma_unassign_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    test_end!();
    ok
}

fn test_dma_get_stream_status() -> bool {
    test_start!();
    let mut streamh: StreamHandle = 0;
    let status = syscall::get_dma_stream_handle(0x2);
    let _ = copy_from_kernel(&mut streamh);
    check_eq!(status, Status::Ok);
    // should fail, not yet supported
    let ok = check_eq!(syscall::dma_get_stream_status(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_start_n_wait_stream() -> bool {
    test_start!();
    let mut ok = true;
    let mut streamh: StreamHandle = 0;
    let mut status : systypes::Status;

    status = syscall::get_dma_stream_handle(0x2);
    let _ = copy_from_kernel(&mut streamh);
    ok &= check_eq!(status, Status::Ok);

    let mut myself: TaskHandle = 0;
    status = syscall::get_process_handle(0xbabe);
    let _ = copy_from_kernel(&mut myself);
    ok &= check_eq!(status, Status::Ok);

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm1h: systypes::ShmHandle = 0;
    let mut info1 = ShmInfo {
        label: 0 as u32,
        handle: 0 as u32,
        base: 0 as usize,
        len: 0 as usize,
        perms: 0 as u32,
    };

    status = syscall::get_shm_handle(shm1.label);
    let _ = copy_from_kernel(&mut shm1h);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::shm_set_credential(
            shm1h,
            myself,
            SHMPermission::Write as u32 | SHMPermission::Map as u32
    );
    ok &= check_eq!(status, Status::Ok);


    status = syscall::map_shm(shm1h);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::shm_get_infos(shm1h);
    let _ = copy_from_kernel(&mut info1);
    ok &= check_eq!(status, Status::Ok);

    if ok {
        unsafe {
            core::ptr::write_bytes(info1.base as *mut u8, 0xa5, 0x100);
        }
    }

    let shm2 = get_shm_by_name("shm_autotest_2").expect("shm_autotest_2 not found");
    let mut info2 = ShmInfo {
        label: 0 as u32,
        handle: 0 as u32,
        base: 0 as usize,
        len: 0 as usize,
        perms: 0 as u32,
    };
    let mut shm2h: systypes::ShmHandle = 0;
    status = syscall::get_shm_handle(shm2.label);
    let _ = copy_from_kernel(&mut shm2h);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::shm_set_credential(
        shm2h,
        myself,
        SHMPermission::Write as u32 | SHMPermission::Map as u32
    );
    ok &= check_eq!(status, Status::Ok);

    status = syscall::map_shm(shm2h);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::shm_get_infos(shm2h);
    let _ = copy_from_kernel(&mut info2);
    ok &= check_eq!(status, Status::Ok);

    if ok {
        unsafe {
            core::ptr::write_bytes(info2.base as *mut u8, 0x42, 0x100);
        }
    }

    status = syscall::dma_assign_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::dma_start_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::wait_for_event(EventType::Dma as u8, -1);
    ok &= check_eq!(status, Status::Ok);

    let cmp = unsafe {
        core::slice::from_raw_parts(info1.base as *const u8, 0x100)
            == core::slice::from_raw_parts(info2.base as *const u8, 0x100)
    };
    ok &= check!(cmp, "SHM1 == SHM2 after DMA copy");

    status = syscall::dma_suspend_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::dma_unassign_stream(streamh);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::unmap_shm(shm1h);
    ok &= check_eq!(status, Status::Ok);

    status = syscall::unmap_shm(shm2h);
    ok &= check_eq!(status, Status::Ok);

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

    ok &= check_eq!(syscall::get_shm_handle(shm), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) == Ok(Status::Ok);
    ok &= check_eq!(syscall::shm_get_infos(shm), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut infos as *mut _ as *mut u8)) == Ok(Status::Ok);

    ok &= check_eq!(syscall::get_dma_stream_handle(0x1), Status::Ok);
    ok &= copy_from_kernel(&mut (&mut streamh as *mut _ as *mut u8)) == Ok(Status::Ok);

    ok &= check_eq!(syscall::dma_get_stream_info(streamh), Status::Ok);
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
