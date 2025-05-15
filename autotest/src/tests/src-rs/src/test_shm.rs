use uapi::exchange::copy_from_kernel;
use uapi::syscall::*;
use uapi::systypes::*;

// Hypothèse : Ces constantes doivent être définies selon les données DTS.
const SHM_MAP_DMAPOOL: ShmLabel = 0;
const SHM_MAP_NODMAPOOL: ShmLabel = 2;
const SHM_NOMAP_DMAPOOL: ShmLabel = 3;

static mut MYSELF: TaskHandle = 0;
static mut IDLE: TaskHandle = 0;

fn test_shm_handle() {
    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    assert_eq!(get_shm_handle(SHM_NOMAP_DMAPOOL), Status::Ok);
    assert_eq!(get_shm_handle(SHM_MAP_NODMAPOOL), Status::Ok);
    assert_eq!(get_shm_handle(0x42), Status::Invalid);
}

fn test_shm_unmap_notmapped() {
    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();
    assert_eq!(unmap_shm(shm), Status::Invalid);
}

fn test_shm_invalidmap() {
    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();
    shm += 42;
    assert_eq!(map_shm(shm), Status::Invalid);
}

fn test_shm_mapdenied() {
    let perms = SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP;
    assert_eq!(get_shm_handle(SHM_NOMAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();
    unsafe {
        assert_eq!(shm_set_credential(shm, MYSELF, perms), Status::Ok);
    }
    assert_eq!(map_shm(shm), Status::Denied);
}

fn test_shm_infos() {
    let mut shm: ShmHandle = 0;
    let mut infos = ShmInfo {
        handle: 0,
        label: 0,
        base: 0,
        len: 0,
        perms: 0,
    };
    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    copy_from_kernel(&mut shm).unwrap();
    assert_eq!(shm_get_infos(shm), Status::Ok);
    copy_from_kernel(&mut infos).unwrap();

    assert_eq!(infos.label, SHM_MAP_DMAPOOL);
    assert_eq!(infos.handle, shm);
}

fn test_shm_creds_on_mapped() {
    let perms_rw = SHM_PERMISSION_MAP | SHM_PERMISSION_WRITE;
    let perms_w = SHM_PERMISSION_WRITE;

    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    unsafe {
        copy_from_kernel(&mut MYSELF).unwrap();
    }

    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();
    unsafe {
        assert_eq!(shm_set_credential(shm, MYSELF, perms_rw), Status::Ok);
    }
    assert_eq!(map_shm(shm), Status::Ok);
    unsafe {
        assert_eq!(shm_set_credential(shm, MYSELF, perms_w), Status::Busy);
    }
    assert_eq!(unmap_shm(shm), Status::Ok);
    unsafe {
        assert_eq!(shm_set_credential(shm, MYSELF, perms_w), Status::Ok);
    }
}

fn test_shm_allows_idle() {
    assert_eq!(get_process_handle(0xcafe), Status::Ok);
    unsafe {
        copy_from_kernel(&mut IDLE).unwrap();
    }

    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();
    let perms = SHM_PERMISSION_TRANSFER;
    unsafe {
        assert_eq!(shm_set_credential(shm, IDLE, perms), Status::Ok);
    }
}

fn test_shm_map_unmappable() {
    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    unsafe {
        copy_from_kernel(&mut MYSELF).unwrap();
    }

    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();
    let perms = SHM_PERMISSION_WRITE;
    unsafe {
        assert_eq!(shm_set_credential(shm, MYSELF, perms), Status::Ok);
    }
    assert_eq!(map_shm(shm), Status::Denied);
}

fn test_shm_mapunmap() {
    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    unsafe {
        copy_from_kernel(&mut MYSELF).unwrap();
    }

    assert_eq!(get_shm_handle(SHM_MAP_DMAPOOL), Status::Ok);
    let mut shm: ShmHandle = 0;
    copy_from_kernel(&mut shm).unwrap();

    let perms = SHM_PERMISSION_WRITE | SHM_PERMISSION_MAP;
    unsafe {
        assert_eq!(shm_set_credential(shm, MYSELF, perms), Status::Ok);
    }

    assert_eq!(map_shm(shm), Status::Ok);
    assert_eq!(unmap_shm(shm), Status::Ok);
}

pub fn test_shm() {
    test_shm_handle();
    test_shm_unmap_notmapped();
    test_shm_invalidmap();
    test_shm_mapdenied();
    test_shm_infos();
    test_shm_creds_on_mapped();
    test_shm_allows_idle();
    test_shm_map_unmappable();
    test_shm_mapunmap();
}
