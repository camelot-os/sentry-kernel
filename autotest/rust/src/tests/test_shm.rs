// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use crate::check_eq;
use crate::tests::devices_utils::get_shm_by_name;
use crate::log_line;
use crate::test_end;
use crate::test_start;
use crate::test_suite_end;
use crate::test_suite_start;

use sentry_uapi::syscall;
use sentry_uapi::systypes;

pub fn run() -> bool {
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

    let mut status: systypes::Status;
    let mut ok: bool = true;

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let shm2 = get_shm_by_name("shm_autotest_2").expect("shm_autotest_2 not found");
    let shm3 = get_shm_by_name("shm_autotest_3").expect("shm_autotest_3 not found");

    status = syscall::get_shm_handle(shm1.label);
    ok &= check_eq!(status, systypes::Status::Ok);
    status = syscall::get_shm_handle(shm2.label);
    ok &= check_eq!(status, systypes::Status::Ok);
    status = syscall::get_shm_handle(shm3.label);
    ok &= check_eq!(status, systypes::Status::Ok);
    status = syscall::get_shm_handle(0x42);
    ok &= check_eq!(status, systypes::Status::Invalid);

    test_end!();
    ok
}

fn test_shm_unmap_notmapped() -> bool {
    test_start!();

    let mut status: systypes::Status;
    let mut shm: systypes::ShmHandle = 0;
    let mut ok: bool = true;
    let mut myself: systypes::TaskHandle = 0;
    let perms : u32;
    perms = (systypes::SHMPermission::Write as u32) + (systypes::SHMPermission::Map as u32);

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut myself);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::shm_set_credential(shm, myself, perms);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::map_shm(shm);
    ok &= check_eq!(status, systypes::Status::Ok);
    status = syscall::unmap_shm(shm);
    ok &= check_eq!(status, systypes::Status::Ok);
    test_end!();
    ok
}

fn test_shm_invalidmap() -> bool {
    test_start!();

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut ok = true;
    let mut status;

    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);
    status = syscall::map_shm(shm + 42);
    ok &= check_eq!(status, systypes::Status::Invalid);
    test_end!();
    ok
}

fn test_shm_mapdenied() -> bool {
    test_start!();

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut myself: systypes::TaskHandle = 0;
    let perms : u32 = systypes::SHMPermission::Write as u32;
    let mut status: systypes::Status;
    let mut ok: bool = true;

    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut myself);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::shm_set_credential(shm, myself, perms);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::map_shm(shm);
    ok &= check_eq!(status, systypes::Status::Denied);

    test_end!();
    ok
}

fn test_shm_infos() -> bool {
    test_start!();

    let mut status: systypes::Status;
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut ok : bool = true;
    let mut infos = systypes::shm::ShmInfo {
        label: 0 as u32,
        handle: 0 as u32,
        base: 0 as usize,
        len: 0 as usize,
        perms: 0 as u32,
    };

    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    status = syscall::shm_get_infos(shm);
    let _ = sentry_uapi::copy_from_kernel(&mut infos);
    ok &= check_eq!(status, systypes::Status::Ok);
    ok &= check_eq!(infos.label, shm1.label);
    ok &= check_eq!(infos.handle, shm);
    ok &= check_eq!(infos.base as u32, shm1.base as u32);
    ok &= check_eq!(infos.len as u32, shm1.len as u32);

    test_end!();
    ok
}

fn test_shm_creds_on_mapped() -> bool {
    test_start!();

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut myself: systypes::TaskHandle = 0;
    let mut ok : bool = true;
    let mut status: systypes::Status;

    // Get the process handle of the test process
    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut myself);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Get the shared memory handle
    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    let mut perms : u32;
    perms = (systypes::SHMPermission::Write as u32) + (systypes::SHMPermission::Map as u32);

    // Set the credential to allow map and write
    status = syscall::shm_set_credential(
        shm,
        myself,
        perms,
    );
    ok &= check_eq!(status, systypes::Status::Ok);

    // Map the shared memory
    status = syscall::map_shm(shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Check that the credential set is refused, as SHM is mapped
    status = syscall::shm_set_credential(shm, myself, (systypes::SHMPermission::Write).into());
    ok &= check_eq!(status, systypes::Status::Busy);

    // Unmap the shared memory
    status = syscall::unmap_shm(shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    // check that the credential can be set again
    status = syscall::shm_set_credential(
        shm,
        myself,
        (systypes::SHMPermission::Write).into()
    );
    ok &= check_eq!(status, systypes::Status::Ok);

    test_end!();
    ok
}


fn test_shm_allows_idle() -> bool {
    test_start!();

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut idle: systypes::TaskHandle = 0;
    let mut ok : bool = true;
    let mut status: systypes::Status;

    // Get the process handle of the idle task
    status = syscall::get_process_handle(0xcafe);
    let _ = sentry_uapi::copy_from_kernel(&mut idle);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Get the shared memory handle
    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Set the credentials to allow transfer to idle task
    status = syscall::shm_set_credential(
        shm,
        idle,
        (systypes::SHMPermission::Transfer).into()
    );
    ok &= check_eq!(status, systypes::Status::Ok);

    test_end!();
    ok
}

fn test_shm_map_unmappable() -> bool {
    test_start!();

    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut myself: systypes::TaskHandle = 0;
    let mut status: systypes::Status;
    let perms = systypes::SHMPermission::Write as u32;
    let mut ok: bool = true;

    // Get the process handle of the test process
    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut myself);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Get the shared memory handle
    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Set the credentials to allow write but not map
    status = syscall::shm_set_credential(shm, myself, perms.into());
    ok &= check_eq!(status, systypes::Status::Ok);

    // Try to map the shared memory, which is not allowed
    status = syscall::map_shm(shm);
    ok &= check_eq!(status, systypes::Status::Denied);

    test_end!();
    ok
}

fn test_shm_mapunmap() -> bool {
    test_start!();
    let shm1 = get_shm_by_name("shm_autotest_1").expect("shm_autotest_1 not found");
    let mut shm: systypes::ShmHandle = 0;
    let mut myself: systypes::TaskHandle = 0;
    let perms = (systypes::SHMPermission::Write as u32) | (systypes::SHMPermission::Map as u32);
    let mut status: systypes::Status;
    let mut ok: bool = true;

    // Get the process handle of the test process
    status = syscall::get_process_handle(0xbabe);
    let _ = sentry_uapi::copy_from_kernel(&mut myself);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Get the shared memory handle
    status = syscall::get_shm_handle(shm1.label);
    let _ = sentry_uapi::copy_from_kernel(&mut shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    // Set the credentials to allow map and write
    status = syscall::shm_set_credential(shm, myself, perms.into());
    ok &= check_eq!(status, systypes::Status::Ok);

    // Map the shared memory
    status = syscall::map_shm(shm);
    ok &= check_eq!(status, systypes::Status::Ok);

    if ok {

        // Check that the shared memory is mapped correctly and writable
        unsafe {
            let shmptr = shm1.base as *mut u32;
            for i in 0..12 {
                shmptr.add(i).write_volatile(i as u32 * 4);
            }
        }

        // Unmap the shared memory
        status = syscall::unmap_shm(shm);
        ok &= check_eq!(status, systypes::Status::Ok);
    }
    test_end!();
    ok
}
