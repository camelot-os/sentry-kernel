use uapi::dma::timer::*;
use uapi::exchange::copy_from_kernel;
use uapi::syscall::*;
use uapi::systypes::EventType;
use uapi::systypes::*;

const EVENT_IRQ: u8 = EventType::Irq as u8;

fn read_irq_from_event_buffer(buf: &[u8]) -> u32 {
    let irq_bytes =
        &buf[core::mem::size_of::<ExchangeHeader>()..core::mem::size_of::<ExchangeHeader>() + 4];
    u32::from_ne_bytes(irq_bytes.try_into().unwrap())
}

fn test_irq_spawn_one_it() {
    let mut buf = [0u8; 128];
    let irq = timer_get_irqn();
    timer_enable_interrupt();
    timer_enable();

    let res = wait_for_event(EVENT_IRQ, 0);
    assert_eq!(res, Status::Ok);
    copy_from_kernel(&mut buf[..]).unwrap();

    let irq_val = read_irq_from_event_buffer(&buf);
    assert_eq!(irq_val, irq);

    let hdr = unsafe { &*(buf.as_ptr() as *const ExchangeHeader) };
    assert_eq!(hdr.source, timer_get_handle());
}

fn test_irq_spawn_two_it() {
    let mut buf = [0u8; 128];
    let irq = timer_get_irqn();

    for _ in 0..2 {
        timer_enable_interrupt();
        timer_enable();

        let res = wait_for_event(EVENT_IRQ, 0);
        assert_eq!(res, Status::Ok);
        copy_from_kernel(&mut buf[..]).unwrap();

        let irq_val = read_irq_from_event_buffer(&buf);
        assert_eq!(irq_val, irq);
    }
}

fn test_irq_spawn_periodic() {
    let mut buf = [0u8; 128];
    let irq = timer_get_irqn();

    timer_enable_interrupt();
    timer_set_periodic();
    timer_enable();

    for count in 0..5 {
        let res = wait_for_event(EVENT_IRQ, 0);
        assert_eq!(res, Status::Ok);
        copy_from_kernel(&mut buf[..]).unwrap();

        let irq_val = read_irq_from_event_buffer(&buf);
        assert_eq!(irq_val, irq);

        if count < 4 {
            timer_enable_interrupt();
        }
    }

    let res = wait_for_event(EVENT_IRQ, 2000);
    assert_eq!(res, Status::Timeout);
}

pub fn test_irq() {
    test_irq_spawn_one_it();
    test_irq_spawn_two_it();
    test_irq_spawn_periodic();
}
