use uapi::exchange::copy_from_kernel;
use uapi::syscall::*;
use uapi::systypes::*;
use uapi::systypes::{EventType, Signal};

const EVENT_SIGNAL: u8 = EventType::Signal as u8;
const TIMEOUT_MS: i32 = 20;

fn test_signal_sendrecv() {
    let mut handle: TaskHandle = 0;
    let mut buffer = [0u8; 128];

    assert_eq!(get_process_handle(0xbabe), Status::Ok);
    copy_from_kernel(&mut handle).unwrap();

    for sig in Signal::Abort as u32..=Signal::Usr2 as u32 {
        let signal = unsafe { core::mem::transmute::<u32, Signal>(sig) };
        assert_eq!(send_signal(handle, signal), Status::Ok);

        let res = wait_for_event(EVENT_SIGNAL, TIMEOUT_MS);
        assert_eq!(res, Status::Ok);

        copy_from_kernel(&mut buffer[..core::mem::size_of::<ExchangeHeader>() + 4]).unwrap();
        let header = unsafe { &*(buffer.as_ptr() as *const ExchangeHeader) };
        let content_bytes = &buffer
            [core::mem::size_of::<ExchangeHeader>()..core::mem::size_of::<ExchangeHeader>() + 4];
        let received_sig = u32::from_ne_bytes(content_bytes.try_into().unwrap());

        assert_eq!(received_sig, signal as u32);
    }
}

pub fn test_signal() {
    test_signal_sendrecv();
}
