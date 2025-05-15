use uapi::devices::{DEV_ID_I2C1, DEVICE_BASEADDR, DEVICE_ID};
use uapi::exchange::copy_from_kernel;
use uapi::syscall::*;
use uapi::systypes::*;

fn test_map_unmap_notmapped() {
    let mut dev: DeviceHandle = 0;
    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_I2C1]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();
    let res = unmap_dev(dev);
    assert_eq!(res, Status::Invalid);
}

fn test_map_invalidmap() {
    let mut dev: DeviceHandle = 0;
    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_I2C1]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();
    dev += 42;
    let res = map_dev(dev);
    assert_eq!(res, Status::Invalid);
}

fn test_map_mapunmap() {
    let mut dev: DeviceHandle = 0;
    assert_eq!(get_device_handle(DEVICE_ID[DEV_ID_I2C1]), Status::Ok);
    copy_from_kernel(&mut dev).unwrap();

    assert_eq!(map_dev(dev), Status::Ok);

    #[cfg(feature = "stm32u5a5")]
    {
        let base = DEVICE_BASEADDR[DEV_ID_I2C1] as *const u32;
        for offset in 0..12 {
            let reg = unsafe { core::ptr::read_volatile(base.add(offset)) };
            if offset == 6 {
                assert_eq!(reg, 0x1);
            } else {
                assert_eq!(reg, 0x0);
            }
        }
    }

    assert_eq!(unmap_dev(dev), Status::Ok);
}

pub fn test_map() {
    test_map_unmap_notmapped();
    test_map_invalidmap();
    test_map_mapunmap();
}
