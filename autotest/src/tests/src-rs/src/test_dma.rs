// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use sentry_uapi::dma::*;
use sentry_uapi::event::EventType;
use sentry_uapi::shm::*;
use sentry_uapi::status::Status;
use sentry_uapi::*;

pub fn test_dma() -> bool {
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
    let ok = check_eq!(__sys_get_dma_stream_handle(0x42), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_manipulate_stream_badhandle() -> bool {
    test_start!();
    let ok = check_eq!(__sys_dma_start_stream(0), Status::Invalid)
        & check_eq!(__sys_dma_suspend_stream(0), Status::Invalid)
        & check_eq!(__sys_dma_get_stream_status(0), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_assign_unassign_stream() -> bool {
    test_start!();
    let mut streamh: DmaHandle = 0;
    let ok = check_eq!(__sys_get_dma_stream_handle(0x2), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut streamh as *mut _ as *mut u8,
                core::mem::size_of::<DmaHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_dma_assign_stream(streamh), Status::Ok)
        & check_eq!(__sys_dma_assign_stream(streamh), Status::Invalid)
        & check_eq!(__sys_dma_unassign_stream(streamh), Status::Ok)
        & check_eq!(__sys_dma_unassign_stream(streamh), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_start_stream() -> bool {
    test_start!();
    let mut streamh: DmaHandle = 0;
    let ok = check_eq!(__sys_get_dma_stream_handle(0x2), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut streamh as *mut _ as *mut u8,
                core::mem::size_of::<DmaHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_dma_start_stream(streamh), Status::Invalid)
        & check_eq!(__sys_dma_assign_stream(streamh), Status::Ok)
        & check_eq!(__sys_dma_start_stream(streamh), Status::Ok)
        & check_eq!(__sys_dma_assign_stream(streamh), Status::Invalid)
        & check_eq!(__sys_dma_start_stream(streamh), Status::Invalid);
    test_end!();
    ok
}

fn test_dma_get_stream_status() -> bool {
    test_start!();
    let mut streamh: DmaHandle = 0;
    let ok = check_eq!(__sys_get_dma_stream_handle(0x2), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut streamh as *mut _ as *mut u8,
                core::mem::size_of::<DmaHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_dma_get_stream_status(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_stop_stream() -> bool {
    test_start!();
    let mut streamh: DmaHandle = 0;
    let ok = check_eq!(__sys_get_dma_stream_handle(0x2), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut streamh as *mut _ as *mut u8,
                core::mem::size_of::<DmaHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_dma_suspend_stream(streamh), Status::Ok)
        & check_eq!(__sys_dma_unassign_stream(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_start_n_wait_stream() -> bool {
    test_start!();
    let mut ok = true;
    let mut streamh: DmaHandle = 0;
    ok &= check_eq!(__sys_get_dma_stream_handle(0x2), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut streamh as *mut _ as *mut u8,
            core::mem::size_of::<DmaHandle>(),
        )
    } == Status::Ok;

    let mut myself: TaskHandle = 0;
    ok &= check_eq!(__sys_get_process_handle(0xbabe), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut myself as *mut _ as *mut u8,
            core::mem::size_of::<TaskHandle>(),
        )
    } == Status::Ok;

    let mut shm1: ShmHandle = 0;
    let mut info1 = ShmInfos::default();
    ok &= check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut shm1 as *mut _ as *mut u8,
            core::mem::size_of::<ShmHandle>(),
        )
    } == Status::Ok;
    ok &= check_eq!(
        __sys_shm_set_credential(shm1, myself, SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP),
        Status::Ok
    );
    ok &= check_eq!(__sys_map_shm(shm1), Status::Ok);
    ok &= check_eq!(__sys_shm_get_infos(shm1), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut info1 as *mut _ as *mut u8,
            core::mem::size_of::<ShmInfos>(),
        )
    } == Status::Ok;
    unsafe {
        core::ptr::write_bytes(info1.base as *mut u8, 0xa5, 0x100);
    }

    let mut shm2: ShmHandle = 0;
    let mut info2 = ShmInfos::default();
    ok &= check_eq!(__sys_get_shm_handle(shms[1].id), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut shm2 as *mut _ as *mut u8,
            core::mem::size_of::<ShmHandle>(),
        )
    } == Status::Ok;
    ok &= check_eq!(
        __sys_shm_set_credential(shm2, myself, SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP),
        Status::Ok
    );
    ok &= check_eq!(__sys_map_shm(shm2), Status::Ok);
    ok &= check_eq!(__sys_shm_get_infos(shm2), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut info2 as *mut _ as *mut u8,
            core::mem::size_of::<ShmInfos>(),
        )
    } == Status::Ok;
    unsafe {
        core::ptr::write_bytes(info2.base as *mut u8, 0x42, 0x100);
    }

    ok &= check_eq!(__sys_dma_assign_stream(streamh), Status::Ok);
    ok &= check_eq!(__sys_dma_start_stream(streamh), Status::Ok);
    ok &= check_eq!(__sys_wait_for_event(EventType::Dma as u8, -1), Status::Ok);

    let cmp = unsafe {
        core::slice::from_raw_parts(info1.base as *const u8, 0x100)
            == core::slice::from_raw_parts(info2.base as *const u8, 0x100)
    };
    ok &= check!(cmp, "SHM1 == SHM2 after DMA copy");

    ok &= check_eq!(__sys_dma_suspend_stream(streamh), Status::Ok);
    ok &= check_eq!(__sys_dma_unassign_stream(streamh), Status::Ok);
    test_end!();
    ok
}

fn test_dma_get_info() -> bool {
    test_start!();
    let mut ok = true;
    let mut streamh: DmaHandle = 0;
    let mut stream_info = GpdmaStreamCfg::default();
    let mut shm: ShmHandle = 0;
    let mut infos = ShmInfos::default();

    ok &= check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut shm as *mut _ as *mut u8,
            core::mem::size_of::<ShmHandle>(),
        )
    } == Status::Ok;
    ok &= check_eq!(__sys_shm_get_infos(shm), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut infos as *mut _ as *mut u8,
            core::mem::size_of::<ShmInfos>(),
        )
    } == Status::Ok;

    ok &= check_eq!(__sys_get_dma_stream_handle(0x1), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut streamh as *mut _ as *mut u8,
            core::mem::size_of::<DmaHandle>(),
        )
    } == Status::Ok;

    ok &= check_eq!(__sys_dma_get_stream_info(streamh), Status::Ok);
    ok &= unsafe {
        copy_from_kernel(
            &mut stream_info as *mut _ as *mut u8,
            core::mem::size_of::<GpdmaStreamCfg>(),
        )
    } == Status::Ok;

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
    ok &= check_eq!(stream_info.circular_source, 1);
    ok &= check_eq!(stream_info.circular_dest, 0);
    ok &= check_eq!(stream_info.priority as u32, GpdmaPriority::Medium as u32);
    test_end!();
    ok
}
