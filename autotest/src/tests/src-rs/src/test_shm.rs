// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::test_log::*;
use uapi::shm::*;
use uapi::status::Status;
use uapi::systypes::*;
use uapi::*;

pub fn test_shm() -> bool {
    test_suite_start!("sys_map_shm");
    let mut ok = true;

    ok &= test_shm_handle();
    ok &= test_shm_invalidmap();
    ok &= test_shm_unmap_notmapped();
    ok &= test_shm_mapunmap();
    ok &= test_shm_map_unmappable();
    ok &= test_shm_mapdenied();
    ok &= test_shm_creds_on_mapped();
    ok &= test_shm_infos();
    ok &= test_shm_allows_idle();

    test_suite_end!("sys_map_shm");
    ok
}

fn test_shm_handle() -> bool {
    test_start!();
    let ok = check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[3].id), Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[2].id), Status::Ok)
        & check_eq!(__sys_get_shm_handle(0x42), Status::Invalid);
    test_end!();
    ok
}

fn test_shm_unmap_notmapped() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let ok = check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_unmap_shm(shm), Status::Invalid);
    test_end!();
    ok
}

fn test_shm_invalidmap() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let ok = check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok);
    let invalid = shm + 42;
    let ok = ok & check_eq!(__sys_map_shm(invalid), Status::Invalid);
    test_end!();
    ok
}
fn test_shm_mapdenied() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;
    let perms = SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP;

    let ok = check_eq!(__sys_get_process_handle(0xbabe), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut myself as *mut _ as *mut u8,
                core::mem::size_of::<TaskHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[3].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_shm_set_credential(shm, myself, perms), Status::Ok)
        & check_eq!(__sys_map_shm(shm), Status::Denied);
    test_end!();
    ok
}

fn test_shm_infos() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let mut infos = ShmInfos::default();

    let ok = check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_shm_get_infos(shm), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut infos as *mut _ as *mut u8,
                core::mem::size_of::<ShmInfos>(),
            )
        } == Status::Ok)
        & check_eq!(infos.label, shms[0].id)
        & check_eq!(infos.handle, shm)
        & check_eq!(infos.base as u32, shms[0].baseaddr as u32)
        & check_eq!(infos.len as u32, shms[0].size as u32);
    test_end!();
    ok
}

fn test_shm_creds_on_mapped() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;

    let ok = check_eq!(__sys_get_process_handle(0xbabe), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut myself as *mut _ as *mut u8,
                core::mem::size_of::<TaskHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(
            __sys_shm_set_credential(shm, myself, SHM_PERMISSION_MAP | SHM_PERMISSION_WRITE),
            Status::Ok
        )
        & check_eq!(__sys_map_shm(shm), Status::Ok)
        & check_eq!(
            __sys_shm_set_credential(shm, myself, SHM_PERMISSION_WRITE),
            Status::Busy
        )
        & check_eq!(__sys_unmap_shm(shm), Status::Ok)
        & check_eq!(
            __sys_shm_set_credential(shm, myself, SHM_PERMISSION_WRITE),
            Status::Ok
        );
    test_end!();
    ok
}
fn test_shm_allows_idle() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let mut idle: TaskHandle = 0;

    let ok = check_eq!(__sys_get_process_handle(0xcafe), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut idle as *mut _ as *mut u8,
                core::mem::size_of::<TaskHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(
            __sys_shm_set_credential(shm, idle, SHM_PERMISSION_TRANSFER),
            Status::Ok
        );
    test_end!();
    ok
}

fn test_shm_map_unmappable() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;
    let perms = SHM_PERMISSION_WRITE;

    let ok = check_eq!(__sys_get_process_handle(0xbabe), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut myself as *mut _ as *mut u8,
                core::mem::size_of::<TaskHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_shm_set_credential(shm, myself, perms), Status::Ok)
        & check_eq!(__sys_map_shm(shm), Status::Denied);
    test_end!();
    ok
}

fn test_shm_mapunmap() -> bool {
    test_start!();
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;
    let perms = SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP;

    let ok = check_eq!(__sys_get_process_handle(0xbabe), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut myself as *mut _ as *mut u8,
                core::mem::size_of::<TaskHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_get_shm_handle(shms[0].id), Status::Ok)
        & (unsafe {
            copy_from_kernel(
                &mut shm as *mut _ as *mut u8,
                core::mem::size_of::<ShmHandle>(),
            )
        } == Status::Ok)
        & check_eq!(__sys_shm_set_credential(shm, myself, perms), Status::Ok)
        & check_eq!(__sys_map_shm(shm), Status::Ok);

    if !ok {
        test_end!();
        return false;
    }

    unsafe {
        let shmptr = shms[0].baseaddr as *mut u32;
        for i in 0..12 {
            shmptr.add(i).write_volatile(i as u32 * 4);
        }
    }

    let ok = ok & check_eq!(__sys_unmap_shm(shm), Status::Ok);
    test_end!();
    ok
}
