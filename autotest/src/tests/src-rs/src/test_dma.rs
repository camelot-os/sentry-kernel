// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use uapi::syscall::*;
use uapi::exchange::copy_from_kernel;
use uapi::systypes::*;
use uapi::systypes::EventType;
use uapi::shms::{SHMS, SHM_PERMISSION_MAP, SHM_PERMISSION_WRITE};

const EVENT_DMA: u8 = EventType::Dma as u8;

static mut MYSELF: TaskHandle = 0;

fn test_dma_get_handle_inval() {
    assert_eq!(get_dma_stream_handle(0x42), Status::Invalid);
}

fn test_dma_manipulate_stream_badhandle() {
    assert_eq!(dma_start_stream(0), Status::Invalid);
    assert_eq!(dma_suspend_stream(0), Status::Invalid);
    assert_eq!(dma_get_stream_status(0), Status::Invalid);
}

fn test_dma_assign_unassign_stream() {
    let stream = get_dma_stream_handle(0x2);
    assert_eq!(stream, Status::Ok);
    let mut streamh: StreamHandle = 0;
    copy_from_kernel(&mut streamh).unwrap();

    assert_eq!(dma_assign_stream(streamh), Status::Ok);
    assert_eq!(dma_assign_stream(streamh), Status::Invalid);
    assert_eq!(dma_unassign_stream(streamh), Status::Ok);
    assert_eq!(dma_unassign_stream(streamh), Status::Invalid);
}

fn test_dma_start_stream() {
    let stream = get_dma_stream_handle(0x2);
    assert_eq!(stream, Status::Ok);
    let mut streamh: StreamHandle = 0;
    copy_from_kernel(&mut streamh).unwrap();

    assert_eq!(dma_start_stream(streamh), Status::Invalid);
    assert_eq!(dma_assign_stream(streamh), Status::Ok);
    assert_eq!(dma_start_stream(streamh), Status::Ok);
    assert_eq!(dma_assign_stream(streamh), Status::Invalid);
    assert_eq!(dma_start_stream(streamh), Status::Invalid);
}

fn test_dma_get_stream_status() {
    let stream = get_dma_stream_handle(0x2);
    assert_eq!(stream, Status::Ok);
    let mut streamh: StreamHandle = 0;
    copy_from_kernel(&mut streamh).unwrap();
    assert_eq!(dma_get_stream_status(streamh), Status::Ok);
}

fn test_dma_stop_stream() {
    let stream = get_dma_stream_handle(0x2);
    assert_eq!(stream, Status::Ok);
    let mut streamh: StreamHandle = 0;
    copy_from_kernel(&mut streamh).unwrap();

    assert_eq!(dma_suspend_stream(streamh), Status::Ok);
    assert_eq!(dma_unassign_stream(streamh), Status::Ok);
}

fn test_dma_start_n_wait_stream() {
    let mut streamh: StreamHandle = 0;
    assert_eq!(get_dma_stream_handle(0x2), Status::Ok);
    copy_from_kernel(&mut streamh).unwrap();

    unsafe {
        assert_eq!(get_process_handle(0xbabe), Status::Ok);
        copy_from_kernel(&mut MYSELF).unwrap();
    }

    // SHM1
    let mut shm1: ShmHandle = 0;
    let mut info1: ShmInfo = Default::default();
    assert_eq!(get_shm_handle(SHMS[0].id), Status::Ok);
    copy_from_kernel(&mut shm1).unwrap();
    unsafe {
        assert_eq!(shm_set_credential(shm1, MYSELF, SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP), Status::Ok);
    }
    assert_eq!(map_shm(shm1), Status::Ok);
    assert_eq!(shm_get_infos(shm1), Status::Ok);
    copy_from_kernel(&mut info1).unwrap();
    unsafe { core::ptr::write_bytes(info1.base as *mut u8, 0xa5, 0x100); }

    // SHM2
    let mut shm2: ShmHandle = 0;
    let mut info2: ShmInfo = Default::default();
    assert_eq!(get_shm_handle(SHMS[1].id), Status::Ok);
    copy_from_kernel(&mut shm2).unwrap();
    unsafe {
        assert_eq!(shm_set_credential(shm2, MYSELF, SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP), Status::Ok);
    }
    assert_eq!(map_shm(shm2), Status::Ok);
    assert_eq!(shm_get_infos(shm2), Status::Ok);
    copy_from_kernel(&mut info2).unwrap();
    unsafe { core::ptr::write_bytes(info2.base as *mut u8, 0x42, 0x100); }

    assert_eq!(dma_assign_stream(streamh), Status::Ok);
    assert_eq!(dma_start_stream(streamh), Status::Ok);
    assert_eq!(wait_for_event(EVENT_DMA, -1), Status::Ok);

    let memcmp = unsafe {
        core::slice::from_raw_parts(info1.base as *const u8, 0x100)
            == core::slice::from_raw_parts(info2.base as *const u8, 0x100)
    };
    assert!(memcmp);

    assert_eq!(dma_suspend_stream(streamh), Status::Ok);
    assert_eq!(dma_unassign_stream(streamh), Status::Ok);
}

fn test_dma_get_info() {
    let stream = get_dma_stream_handle(0x1);
    assert_eq!(stream, Status::Ok);
    let mut streamh: StreamHandle = 0;
    copy_from_kernel(&mut streamh).unwrap();

    let mut info: uapi::dma::GpdmaStreamCfg = Default::default();
    let mut shm: ShmHandle = 0;
    let mut shm_info: ShmInfo = Default::default();

    assert_eq!(get_shm_handle(SHMS[0].id), Status::Ok);
    copy_from_kernel(&mut shm).unwrap();
    assert_eq!(shm_get_infos(shm), Status::Ok);
    copy_from_kernel(&mut shm_info).unwrap();

    assert_eq!(dma_get_stream_info(streamh), Status::Ok);
    copy_from_kernel(&mut info).unwrap();

    assert_eq!(info.stream, 112);
    assert_eq!(info.channel, 1);
    assert_eq!(info.controller, 0);
    assert_eq!(info.transfer_type, GpdmaTransferType::DeviceToMemory);
    assert_eq!(info.transfer_len, 42);
    assert_eq!(info.source, 0);
    assert_eq!(info.dest, shm_info.base);
    assert_eq!(info.circular_source, 1);
    assert_eq!(info.circular_dest, 0);
    assert_eq!(info.priority, GpdmaPriority::Medium);
}

pub fn test_dma() {
    test_dma_get_handle_inval();
    test_dma_manipulate_stream_badhandle();
    test_dma_assign_unassign_stream();
    test_dma_start_stream();
    test_dma_get_stream_status();
    test_dma_stop_stream();
    test_dma_start_n_wait_stream();
    test_dma_get_info();
}

