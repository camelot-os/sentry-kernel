use uapi::exchange::{copy_from_kernel, copy_to_kernel};
use uapi::syscall::*;
use uapi::systypes::EventType;
use uapi::systypes::*;

const EVENT_IPC: u8 = EventType::Ipc as u8;
const TIMEOUT_MS: i32 = 100;
const MSG: &[u8] = b"hello it's autotest";

fn test_ipc_send_toobig() {
    let mut handle: TaskHandle = 0;
    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    copy_from_kernel(&mut handle).unwrap();

    let too_large_len = (exchange::length() + 1) as u8;
    assert_eq!(send_ipc(handle, too_large_len), Status::Invalid);

    let almost_max_len = 255;
    assert_eq!(send_ipc(handle, almost_max_len), Status::Invalid);
}

fn test_ipc_send_invalidtarget() {
    let invalid_target: TaskHandle = 0xdead_1001;
    let res = send_ipc(invalid_target, 20);
    assert_eq!(res, Status::Invalid);
}

fn test_ipc_sendrecv() {
    let mut handle: TaskHandle = 0;
    let mut buffer = [0u8; 128];

    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    copy_from_kernel(&mut handle).unwrap();

    copy_to_kernel(MSG).unwrap();
    assert_eq!(send_ipc(handle, 20), Status::Ok);

    let res = wait_for_event(EVENT_IPC, TIMEOUT_MS);
    assert_eq!(res, Status::Ok);

    copy_from_kernel(&mut buffer[..24]).unwrap();
    let header = unsafe { &*(buffer.as_ptr() as *const ExchangeHeader) };
    let data_ptr = unsafe {
        core::slice::from_raw_parts(
            buffer.as_ptr().add(core::mem::size_of::<ExchangeHeader>()),
            header.length as usize,
        )
    };

    assert_eq!(header.event, EventType::Ipc.into());
    assert_eq!(&data_ptr[..], &MSG[..20]);
}

fn test_ipc_deadlock() {
    let mut handle: TaskHandle = 0;
    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    copy_from_kernel(&mut handle).unwrap();

    copy_to_kernel(MSG).unwrap();
    assert_eq!(send_ipc(handle, 20), Status::Ok);

    copy_to_kernel(MSG).unwrap();
    assert_eq!(send_ipc(handle, 20), Status::Deadlock);
}

pub fn test_ipc() {
    test_ipc_send_toobig();
    test_ipc_send_invalidtarget();
    test_ipc_sendrecv();
    test_ipc_deadlock();
}
