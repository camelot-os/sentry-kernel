// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::devices_utils::get_shm_by_name;
use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;
use core::prelude::v1::Ok;
use sentry_uapi::syscall::get_process_handle;
use sentry_uapi::syscall::get_shm_handle;
use sentry_uapi::syscall::map_shm;
use sentry_uapi::syscall::shm_get_infos;
use sentry_uapi::syscall::shm_set_credential;
use sentry_uapi::syscall::unmap_shm;
use sentry_uapi::systypes::SHMPermission;
use sentry_uapi::systypes::ShmHandle;
use sentry_uapi::systypes::Status;
use sentry_uapi::systypes::*;
use sentry_uapi::*;

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
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let shm2 = get_shm_by_name("shm_autotest_2").expect("shm_autotest_2 not found");
    let shm3 = get_shm_by_name("shm_autotest_3").expect("shm_autotest_3 not found");
    let ok = check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & check_eq!(get_shm_handle(shm2.id), Status::Ok)
        & check_eq!(get_shm_handle(shm3.id), Status::Ok)
        & check_eq!(get_shm_handle(0x42), Status::Invalid);
    test_end!();
    ok
}

fn test_shm_unmap_notmapped() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let ok = check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(unmap_shm(shm), Status::Invalid);
    test_end!();
    ok
}

fn test_shm_invalidmap() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let ok = check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok));
    let invalid = shm + 42;
    let ok = ok & check_eq!(map_shm(invalid), Status::Invalid);
    test_end!();
    ok
}
fn test_shm_mapdenied() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;
    let perms = SHMPermission::Write | SHMPermission::Map;

    let ok = check_eq!(get_process_handle(0xbabe), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut myself as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(shm_set_credential(shm, myself, perms.into()), Status::Ok)
        & check_eq!(map_shm(shm), Status::Denied);
    test_end!();
    ok
}

fn test_shm_infos() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let mut infos = ShmInfos::default();

    let ok = check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(shm_get_infos(shm), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut infos as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(infos.label, shm1.id)
        & check_eq!(infos.handle, shm)
        & check_eq!(infos.base as u32, shm1.baseaddr as u32)
        & check_eq!(infos.len as u32, shm1.size as u32);
    test_end!();
    ok
}

fn test_shm_creds_on_mapped() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;

    let ok = check_eq!(get_process_handle(0xbabe), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut myself as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(
            shm_set_credential(
                shm,
                myself,
                (SHMPermission::Map | SHMPermission::Write).into()
            ),
            Status::Ok
        )
        & check_eq!(map_shm(shm), Status::Ok)
        & check_eq!(
            shm_set_credential(shm, myself, (SHMPermission::Write).into()),
            Status::Busy
        )
        & check_eq!(unmap_shm(shm), Status::Ok)
        & check_eq!(
            shm_set_credential(shm, myself, (SHMPermission::Write).into()),
            Status::Ok
        );
    test_end!();
    ok
}
fn test_shm_allows_idle() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let mut idle: TaskHandle = 0;

    let ok = check_eq!(get_process_handle(0xcafe), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut idle as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(
            shm_set_credential(shm, idle, (SHMPermission::Transfer).into()),
            Status::Ok
        );
    test_end!();
    ok
}

fn test_shm_map_unmappable() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;
    let perms = SHMPermission::Write;

    let ok = check_eq!(get_process_handle(0xbabe), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut myself as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(shm_set_credential(shm, myself, perms.into()), Status::Ok)
        & check_eq!(map_shm(shm), Status::Denied);
    test_end!();
    ok
}

fn test_shm_mapunmap() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: ShmHandle = 0;
    let mut myself: TaskHandle = 0;
    let perms = SHMPermission::Write | SHMPermission::Map;

    let ok = check_eq!(get_process_handle(0xbabe), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut myself as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(get_shm_handle(shm1.id), Status::Ok)
        & (unsafe { copy_from_kernel(&mut (&mut shm as *mut _ as *mut u8)) } == Ok(Status::Ok))
        & check_eq!(shm_set_credential(shm, myself, perms.into()), Status::Ok)
        & check_eq!(map_shm(shm), Status::Ok);

    if !ok {
        test_end!();
        return false;
    }

    unsafe {
        let shmptr = shm1.baseaddr as *mut u32;
        for i in 0..12 {
            shmptr.add(i).write_volatile(i as u32 * 4);
        }
    }

    let ok = ok & check_eq!(unmap_shm(shm), Status::Ok);
    test_end!();
    ok
}
