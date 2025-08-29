// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

/// This library defines types (structs, enums, ...) related to syscalls,
/// that need to be shared between the kernel and the uapi.
///
/// Most important enum is `Syscall`, which defines the list of available
/// syscalls and sets their identifier/number.
///
/// This macro takes an enum and implements fallible conversion from a u8
/// exhaustively, as required by the SVC Handler.
///
/// ```
/// pub enum Syscall {
///     Exit,
/// }
///
/// impl TryFrom<u8> for Syscall {
///     type Error = ();
///     fn try_from(v: u8) -> Result<Self, Self::Error> {
///         match v {
///             x if x == Syscall::Exit as u8 => Ok(Syscall::Exit),
///             _ => Err(())
///         }
///     }
/// }
/// ```
/// (inspired by https://stackoverflow.com/a/58715864)
///
/// It also ensures that there cannot be a mismatch between the u8 value
/// used to define the enum, and the value used for converting to it.
macro_rules! syscall_list {
    ($vis:vis enum $name:ident {
        $($vname:ident,)*
    }) => {
        #[repr(C)]
        #[cfg_attr(debug_assertions, derive(Debug))]
        $vis enum $name {
            $($vname,)*
        }

        impl TryFrom<u8> for $name {
            type Error = Status;

            fn try_from(v: u8) -> Result<Self, Self::Error> {
                match v {
                    $(x if x == $name::$vname as u8 => Ok($name::$vname),)*
                    _ => Err(Status::Invalid),
                }
            }
        }
    }
}

syscall_list! {
pub enum Syscall {
    Exit,
    GetProcessHandle,
    GetDeviceHandle,
    Yield,
    Sleep,
    Start,
    MapDev,
    MapShm,
    UnmapDev,
    UnmapShm,
    SHMSetCredential,
    SendIPC,
    SendSignal,
    WaitForEvent,
    PmManage,
    PmSetClock,
    Log,
    Alarm,
    GetRandom,
    GetCycle,
    GpioGet,
    GpioSet,
    GpioReset,
    GpioToggle,
    GpioConfigure,
    IrqAcknowledge,
    IrqEnable,
    IrqDisable,
    GetShmHandle,
    GetDmaStreamHandle,
    DmaStartStream,
    DmaSuspendStream,
    DmaGetStreamStatus,
    ShmGetInfos,
    DmaAssignStream,
    DmaUnassignStream,
    DmaGetStreamInfo,
    DmaResumeStream,
}
}

macro_rules! mirror_enum {
    ($to:ty, $vis:vis enum $name:ident {
        $($vname:ident,)*
    }) => {
        #[repr(C)]
        $vis enum $name {
            $($vname,)*
        }

        impl TryFrom<$to> for $name {
            type Error = Status;

            fn try_from(v: $to) -> Result<Self, Self::Error> {
                match v {
                    $(x if x == $name::$vname as $to => Ok($name::$vname),)*
                    _ => Err(Status::Invalid),
                }
            }
        }
    }
}

/// Sentry syscall return values
///
/// Note: the kernel also hold, at kernel level, another value denoted
/// 'NonSense'. This value must never be returned to userspace. This
/// is why this value do not exist here.
///
/// Such a return should raise a security exception. All syscalls that can't set
/// they return code synchronously (e.g. IPC), MUST use this value as
/// default one
#[repr(C)]
#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(Copy, Clone, PartialEq)]
pub enum Status {
    /// Successful result, the kernel has terminated its task with no error
    Ok,
    /// At least one parameter is not valid (not allowed or not found)
    Invalid,
    /// The requested action is not allowed for caller, or the resource is not owned
    Denied,
    /// The requested resource do not exist
    NoEntity,
    /// The requested resource is in a state that do now allow the current call
    Busy,
    /// The requested resource is already mapped
    AlreadyMapped,
    /// Critical (mostly security-related) unexpected event
    Critical,
    /// The requested resource did not respond or the call has reached its maximum wait time
    Timeout,
    /// The requested resource is not here yet, come back later
    Again,
    /// The call has been interrupted sooner than expected. Used for blocking calls
    Intr,
    /// The requested resource can't be manipulated without generating a dead lock
    Deadlk,
}

/// u32 to Status converter, required to support register encoded value
impl From<u32> for Status {
    fn from(status_int: u32) -> Status {
        match status_int {
            0 => Status::Ok,
            1 => Status::Invalid,
            2 => Status::Denied,
            3 => Status::NoEntity,
            4 => Status::Busy,
            5 => Status::AlreadyMapped,
            6 => Status::Critical,
            7 => Status::Timeout,
            8 => Status::Again,
            9 => Status::Intr,
            10 => Status::Deadlk,
            _ => panic!(),
        }
    }
}

/// A process label is a development-time fixed identifier that can be used hardcoded
///  in the source code. This can be used in order to get back remote process effective
/// identifier from label at any time in order to communicate
pub type TaskLabel = u32;

/// A shm label is a development-time fixed identifier that can be used hardcoded
/// in the source code. This label is set in the device-tree in the shm declaration,
/// and can be used in order to get back the effective shm handler from it in order
/// to manipulate it
pub type ShmLabel = u32;

/// A stream label is a development-time fixed identifier that can be used hardcoded
/// in the source code in order to identify declared DMA streams.
/// This label is set in the device-tree in the stream declaration,
/// and can be used in order to get back the effective DMA stream handler from it in order
/// to manipulate it
pub type StreamLabel = u32;

/// A device label is a development-time fixed identifier that can be used hardcoded
/// in the source code in order to identify declared device.
/// This label is, by now, the result of the device tree analysis but will be replaced by
/// a clean sentry,label field at dts level, in the same way other label are set, to
/// highly simplify userspace level usage.
/// This label is used to get back the associated handle at run time.
pub type DeviceLabel = u32;

/// A device handle is a unique identifier required to manipulate a devive
///
/// That handle is forged by the kernel at bootup time and vary from one boot to another.
/// The device handle can be retrieved by using the [`crate::syscall::get_device_handle`]
/// syscall.
///
pub type DeviceHandle = u32;

/// A task handle is a unique identifier required to communicate with another task.
///
/// A task handle is associated to a job, meaning that if a task job terminates and
/// is restarted, the associated handle is reforged and diverge from the previous one.
///
/// All jobs have a task handle. This handle is the only way to uniquely identify a
/// given job with which we need to communicate..
/// The task handle can be retrieved by using the [`crate::syscall::get_process_handle`]
/// syscall.
///
pub type TaskHandle = u32;

/// A SHM handle is a unique identifier required to manipulate a shared memory.
///
/// That handle is forged by the kernel at bootup time and vary from one boot to another.
/// The SHM handle can be retrieved by using the [`crate::syscall::get_shm_handle`]
/// syscall.
///
pub type ShmHandle = u32;

/// A DMA stream handle is a unique identifier required to manipulate a DMA stream.
///
/// That handle is forged by the kernel at bootup time and vary from one boot to another.
/// The DMA stream handle can be retrieved by using the [`crate::syscall::get_dma_stream_handle`]
/// syscall.
///
pub type StreamHandle = u32;

/// Definition of Sentry events
///
/// Multiple events can targets a given task. These events are strictly
/// identified so that the task can easily differentiate them.
///
/// As multiple events can be set at once, event field is using a
/// bitfield model to keep C+Rust usage easy
#[repr(C)]
#[derive(Clone, PartialEq, Copy, Debug)]
pub enum EventType {
    /// No event
    None = 0,
    /// Inter-task slow path IPC event
    Ipc = 1,
    /// Inter-task signal event
    Signal = 2,
    /// Hardware interrupt event
    Irq = 4,
    /// DMA stream event
    Dma = 8,
    /// Any of the above events
    All = 15,
}

/// list of potential Event types, encoded as u8 to exchange with kernel
///
/// This value corresponds to a set of one or multiple EventType value, so
/// that the job can wait for multiple events at a time.
/// Events priority when returning from the kernel is described in the events
/// chapter of the Sentry documentation.
///
pub type EventList = u8;

impl From<EventType> for u8 {
    fn from(event: EventType) -> u8 {
        match event {
            EventType::None => 0,
            EventType::Ipc => 1,
            EventType::Signal => 2,
            EventType::Irq => 4,
            EventType::Dma => 8,
            EventType::All => 15,
        }
    }
}

impl From<u8> for EventType {
    fn from(event: u8) -> EventType {
        match event {
            0 => EventType::None,
            1 => EventType::Ipc,
            2 => EventType::Signal,
            4 => EventType::Irq,
            8 => EventType::Dma,
            15 => EventType::All,
            _ => EventType::None,
        }
    }
}
/// Erase type that can be used to clear the SVC_Exchange.
///
/// TODO: to be moved to svc_exchange module as used exclusively by
/// this module primitives.
///
/// There are two types of erase model:
/// - Zeroify, that write 0x0 pattern in the SVC exchange zone
/// - Random, that write a random pattern
///
/// By now, only Zeroify is supported.
#[repr(C)]
pub enum EraseType {
    Zeroify = 0x5a,
    Random = 0xa5,
}

impl From<EraseType> for u32 {
    fn from(etype: EraseType) -> u32 {
        match etype {
            EraseType::Zeroify => 0x5a,
            EraseType::Random => 0xa5,
        }
    }
}

/// Erase mode that can be used to clear the SVC_Exchange.
///
/// There are two types of erase mode:
/// - UserErase, leaving the write action to the UAPI crate, withtout kernel call
/// - KernelErase, requiring the kernel to execute the erasing.
///   This last mode ensure that the erasing is atomic while it is started.
///
/// By now, only UserErase ils supported.
#[repr(C)]
pub enum EraseMode {
    UserErase = 0x72,
    KernelErase = 0x27,
}

impl From<EraseMode> for u32 {
    fn from(emode: EraseMode) -> u32 {
        match emode {
            EraseMode::UserErase => 0x72,
            EraseMode::KernelErase => 0x27,
        }
    }
}

/// Alarm type for alarm-related API
#[repr(C)]
pub enum AlarmFlag {
    /// Start an alarm
    AlarmStart,
    /// Start a periodic alarm
    AlarmStartPeriodic,
    /// Stop an alarm, being periodic or not
    AlarmStop,
}

impl From<AlarmFlag> for u32 {
    fn from(mode: AlarmFlag) -> u32 {
        match mode {
            AlarmFlag::AlarmStart => 0,
            AlarmFlag::AlarmStartPeriodic => 1,
            AlarmFlag::AlarmStop => 2,
        }
    }
}

/// Permission model definition for shared memories
#[repr(C)]
pub enum SHMPermission {
    /// allows target process to map the SHM. No read nor write though
    Map = 0x1,

    /// allows target process to read the mapped SHM. Requires MAP
    Read = 0x2,

    /// allows target process to write shared memory. Requires MAP
    Write = 0x4,

    /// allows target process to transfer SHM to another, pre-allowed, process
    Transfer = 0x8,
}

/// Converter for SHM permission to register encoding (u32)
impl From<SHMPermission> for u32 {
    fn from(shm_perm: SHMPermission) -> u32 {
        match shm_perm {
            SHMPermission::Map => 0x1,
            SHMPermission::Read => 0x2,
            SHMPermission::Write => 0x4,
            SHMPermission::Transfer => 0x8,
        }
    }
}

/// Sentry signals definition. Most of them are aligned on standard POSIX signals
#[repr(C)]
#[derive(Clone, PartialEq, Copy, Debug)]
pub enum Signal {
    /// Abort signal
    Abort = 1,

    /// Timer (from alarm)
    Alarm,

    /// Bus error (bad memory access, memory required)
    Bus,

    /// Continue if previously stopped
    Cont,

    /// Illegal instruction. Can be also used for upper provtocols
    Ill,

    /// I/O now ready
    Io,

    /// Broken pipe
    Pipe,

    /// Event pollable
    Poll,

    /// Termination signal
    Term,

    /// Trace/bp signal (debug usage only)
    Trap,

    /// 1st user-defined signal
    Usr1,

    /// 2nd user-defined signal
    Usr2,

    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User hardfault detected
    PanicUserHardFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: A panic() has been reached in kernel handler
    PanicKernelHardFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User bus fault detected
    PanicUserBusFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel bus fault detected
    PanicKernelBusFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User user usage fault detected
    PanicUserUsageFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel usage fault detected
    PanicKernelUsageFault,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: User memory fault detected
    PanicUserMemAccess,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel memoryfault detected
    PanicKernelMemAccess,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Invalid userspace input received
    PanicKernelInvalidUserspaceInput,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Memory limit reached in a kernel buffer
    PanicKernelShorterKBuffersConfig,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: A given manager returns invalid state error
    PanicKernelInvalidManagerState,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: A given manager return an invalid response
    PanicKernelInvalidManagerResponse,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel handler as reach timeout limit
    PanicKernelTimeout,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel CFI violation
    PanicKernelBadCFICalculation,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Kernel-related hardware IP (MPU, etc.) is in invalid state
    PanicHardwareInvalidState,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: An unexpected modification of a kernel context has been detected
    PanicHardwareUnexpectedModification,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Requested kernel autotest has finished successfully
    AutotestDone,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Requested kernel autotest has finished with a failure
    AutotestFailed,
    #[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
    /// Autotest-specific: Requested kernel autotest has timed-out
    AutotestTimedOut,
}

/// Sleep durations input values for the sleep API
#[repr(C)]
pub enum SleepDuration {
    /// Sleep for 1ms
    D1ms,
    /// Sleep for 2ms
    D2ms,
    /// Sleep for 5ms
    D5ms,
    /// Sleep for 10ms
    D10ms,
    /// Sleep for 20ms
    D20ms,
    /// Sleep for 50ms
    D50ms,
    /// Sleep for a user-specificed number of ms (>0)
    ArbitraryMs(u32),
}

/// Converter for SleepDuration type to register-encoded value
impl From<SleepDuration> for u32 {
    fn from(duration: SleepDuration) -> u32 {
        match duration {
            SleepDuration::D1ms => 1,
            SleepDuration::D2ms => 2,
            SleepDuration::D5ms => 5,
            SleepDuration::D10ms => 10,
            SleepDuration::D20ms => 20,
            SleepDuration::D50ms => 50,
            SleepDuration::ArbitraryMs(v) => v,
        }
    }
}

/// Sleep mode requested
#[repr(C)]
pub enum SleepMode {
    /// Sleep in shallow mode. External events awake the job
    Shallow,
    /// Sleep in deep mode. No sleep interruption
    Deep,
}

/// Converter for SleepMode type to register-encoded value
impl From<SleepMode> for u32 {
    fn from(mode: SleepMode) -> u32 {
        match mode {
            SleepMode::Shallow => 0,
            SleepMode::Deep => 1,
        }
    }
}

/// Converter from register-encoded or C FFI defined value to SleepMode
impl TryFrom<u32> for SleepMode {
    type Error = Status;
    fn try_from(mode: u32) -> Result<SleepMode, Self::Error> {
        match mode {
            0 => Ok(SleepMode::Shallow),
            1 => Ok(SleepMode::Deep),
            _ => Err(Status::Invalid),
        }
    }
}

/// Low power configuration support, defining the CPU sleep state exit event
///
/// There are multiple HW events that may terminate a low-power hardware cycle.
/// These are separated in two main families:
///
/// - Interrupt event (external interrupt)
/// - external event (not interrupt related)
///
/// Moreover, there is some time when the CPU must NOT enter sleep mode for a
/// given amount of time. This can be set with this CPUSleep configuration state.
///
/// > **FIXME**: the sleep trigger and the sleep constraints shoud be defined in separated
/// > types and calls.
#[repr(C)]
pub enum CPUSleep {
    /// Enter sleep mode and wait for external interrupt
    WaitForInterrupt,
    /// Enter sleep mode and wait for external event
    WaitForEvent,
    /// Disable any enter to the low power mode
    ForbidSleep,
    /// Re-enable low power
    AllowSleep,
}

impl From<CPUSleep> for u32 {
    fn from(mode: CPUSleep) -> u32 {
        match mode {
            CPUSleep::WaitForInterrupt => 0,
            CPUSleep::WaitForEvent => 1,
            CPUSleep::ForbidSleep => 2,
            CPUSleep::AllowSleep => 3,
        }
    }
}

impl TryFrom<u32> for CPUSleep {
    type Error = Status;
    fn try_from(mode: u32) -> Result<CPUSleep, Self::Error> {
        match mode {
            0 => Ok(CPUSleep::WaitForInterrupt),
            1 => Ok(CPUSleep::WaitForEvent),
            2 => Ok(CPUSleep::ForbidSleep),
            3 => Ok(CPUSleep::AllowSleep),
            _ => Err(Status::Invalid),
        }
    }
}

mirror_enum! {
    u32,
    pub enum Precision {
        Cycle,
        Nanoseconds,
        Microseconds,
        Milliseconds,
    }
}

/// Header received from the kernel when waiting for at one event type
///
/// Received when returning from [`crate::syscall::wait_for_event`] syscall with
/// a [`Status::Ok`] value.
/// The kernel return data for a single event type at a time, store in event field,
/// while wait_for_event() allows waiting for multiple event at a time.
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct ExchangeHeader {
    pub event: u8,
    pub length: u8,
    pub magic: u16,
    pub peer: u32,
}

#[test]
fn test_layout_exchange_header() {
    const UNINIT: ::std::mem::MaybeUninit<ExchangeHeader> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<ExchangeHeader>(),
        8usize,
        concat!("Size of: ", stringify!(ExchangeHeader))
    );
    assert_eq!(
        ::std::mem::align_of::<ExchangeHeader>(),
        4usize,
        concat!("Alignment of ", stringify!(ExchangeHeader))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).event) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(ExchangeHeader),
            "::",
            stringify!(event)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).length) as usize - ptr as usize },
        1usize,
        concat!(
            "Offset of field: ",
            stringify!(ExchangeHeader),
            "::",
            stringify!(length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).magic) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(ExchangeHeader),
            "::",
            stringify!(magic)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).peer) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(ExchangeHeader),
            "::",
            stringify!(peer)
        )
    );
}

impl ExchangeHeader {
    pub fn is_valid(self) -> bool {
        // TODO: hard-coded by now
        self.magic == 0x4242
    }
}

/// Typical Event received by the kernel using the copy_from_kernel(my_event)
///
/// Event is SentryExchangeable, see [`crate::exchange::SentryExchangeable`] and
/// the corresponding implementation for this struct for more information.
///
#[derive(Debug)]
pub struct Event<'a> {
    pub header: ExchangeHeader,
    pub data: &'a mut [u8],
}

/// Device related types definitions
pub mod dev {

    #[repr(C)]
    #[derive(Debug, Copy, Clone)]
    pub struct InterruptInfo {
        /// interrupt number
        pub it_num: u16,
        /// interrupt controler identifier
        pub it_controler: u8,
    }

    #[test]
    fn test_layout_it_info() {
        const UNINIT: ::std::mem::MaybeUninit<InterruptInfo> = ::std::mem::MaybeUninit::uninit();
        let ptr = UNINIT.as_ptr();
        assert_eq!(
            ::std::mem::size_of::<InterruptInfo>(),
            4usize,
            concat!("Size of: ", stringify!(InterruptInfo))
        );
        assert_eq!(
            ::std::mem::align_of::<InterruptInfo>(),
            2usize,
            concat!("Alignment of ", stringify!(InterruptInfo))
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).it_num) as usize - ptr as usize },
            0usize,
            concat!(
                "Offset of field: ",
                stringify!(InterruptInfo),
                "::",
                stringify!(num)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).it_controler) as usize - ptr as usize },
            2usize,
            concat!(
                "Offset of field: ",
                stringify!(InterruptInfo),
                "::",
                stringify!(controller)
            )
        );
    }

    #[repr(C)]
    #[derive(Copy, Clone, Debug)]
    pub struct IoInfo {
        pub port: u8,
        pub pin: u8,
        pub mode: u8,
        pub af: u8,
        pub ppull: u8,
        pub speed: u8,
        pub pupdr: u8,
    }

    /// userspace oriented device definition
    ///
    #[repr(C)]
    #[derive(Debug, Copy, Clone)]
    pub struct DevInfo {
        pub id: u8,
        /// mappable device. Direct-IO (LED...) are not
        /// Not parsed from the DTS, useless ?
        pub mappable: bool,
        /// for mappable devices, base address
        pub baseaddr: usize,
        /// for mappable devices, mapped size */\n/**<\n  number of device's interrupt.
        /// Can be EXTI (button) or NVIC interrupts (SoC device)
        pub size: usize,
        /// number of device interrupts
        pub num_interrupt: u8,
        /// device interrupt list
        pub its: [InterruptInfo; 8usize],
        /// number of device I/O (pinmux)
        pub num_ios: u8,
        /// device I/O list
        pub ios: [IoInfo; 8usize],
    }
}

/// SHM related types definitions
pub mod shm {

    #[repr(C)]
    #[derive(PartialEq, Debug, Copy, Clone)]
    pub struct ShmInfo {
        pub handle: crate::systypes::ShmHandle,
        pub label: u32,
        pub base: usize,
        pub len: usize,
        pub perms: u32,
    }

    #[test]
    fn test_layout_shm_infos() {
        const UNINIT: ::std::mem::MaybeUninit<ShmInfo> = ::std::mem::MaybeUninit::uninit();
        let ptr = UNINIT.as_ptr();
        assert_eq!(
            ::std::mem::size_of::<ShmInfo>(),
            32usize,
            concat!("Size of: ", stringify!(ShmInfo))
        );
        assert_eq!(
            ::std::mem::align_of::<ShmInfo>(),
            8usize,
            concat!("Alignment of ", stringify!(ShmInfo))
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).handle) as usize - ptr as usize },
            0usize,
            concat!(
                "Offset of field: ",
                stringify!(ShmInfo),
                "::",
                stringify!(handle)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).label) as usize - ptr as usize },
            4usize,
            concat!(
                "Offset of field: ",
                stringify!(shm_infos),
                "::",
                stringify!(label)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).base) as usize - ptr as usize },
            8usize,
            concat!(
                "Offset of field: ",
                stringify!(shm_infos),
                "::",
                stringify!(base)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).len) as usize - ptr as usize },
            16usize,
            concat!(
                "Offset of field: ",
                stringify!(shm_infos),
                "::",
                stringify!(len)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).perms) as usize - ptr as usize },
            24usize,
            concat!(
                "Offset of field: ",
                stringify!(shm_infos),
                "::",
                stringify!(perms)
            )
        );
    }
}

/// DMA related types definitions
///
/// In order to help with proper hierarchy of types for Sentry UAPI, syscall families
/// that requires a lot of shared types. This is the case of the DMA subsystem for
/// which all related types and types helpers are stored in the dma submodule.
pub mod dma {
    // FIXME: this enum is used for bitfield-based manipulation, as the
    // interrupts field is a local OR of this enumerate values
    pub enum GpdmaChanInt {
        /// DMA channel trigger on transfer complete
        TransferComplete = 1,
        /// DMA channel trigger on half transfer and transfer complete
        HalfTransfer = 2,
        /// triggers on DMA transfer or config error, get status for complete information
        DmaError = 4,
    }

    // FIXME: the interrupts field is a bitfield of one to 3 possible interrupts
    // we mai consider intlevels (TC+Error, TC+HT+Error, etc.) meaning that the field
    // is no more a bitfield
    impl TryFrom<u8> for GpdmaChanInt {
        type Error = crate::systypes::Status;
        fn try_from(mode: u8) -> Result<GpdmaChanInt, Self::Error> {
            match mode {
                1 => Ok(GpdmaChanInt::TransferComplete),
                2 => Ok(GpdmaChanInt::HalfTransfer),
                4 => Ok(GpdmaChanInt::DmaError),
                _ => Err(crate::systypes::Status::Invalid),
            }
        }
    }

    pub enum GpdmaTransferType {
        MemoryToDevice = 0,
        DeviceToMemory = 1,
        MemoryToMemory = 2,
        DeviceToDevice = 3,
    }

    impl TryFrom<u16> for GpdmaTransferType {
        type Error = crate::systypes::Status;
        fn try_from(mode: u16) -> Result<GpdmaTransferType, Self::Error> {
            match mode {
                0 => Ok(GpdmaTransferType::MemoryToDevice),
                1 => Ok(GpdmaTransferType::DeviceToMemory),
                2 => Ok(GpdmaTransferType::MemoryToMemory),
                3 => Ok(GpdmaTransferType::DeviceToDevice),
                _ => Err(crate::systypes::Status::Invalid),
            }
        }
    }

    // FIXME: this is a bitmask. We may consider moving to enum value instead
    // for e.g. by using IncrementBoth = 3
    pub enum GpdmaTransferMode {
        IncrementNone = 0,
        IncrementSrc = 1,
        IncrementDest = 2,
    }

    pub enum GpdmaBeatLen {
        /// Data len to manipulate is in bytes
        Byte = 0,
        /// Data len to manipulate is in half word
        Halfword = 1,
        /// Data len to manipulate is in word
        Word = 2,
    }

    impl TryFrom<u8> for GpdmaBeatLen {
        type Error = crate::systypes::Status;
        fn try_from(mode: u8) -> Result<GpdmaBeatLen, Self::Error> {
            match mode {
                0 => Ok(GpdmaBeatLen::Byte),
                1 => Ok(GpdmaBeatLen::Halfword),
                2 => Ok(GpdmaBeatLen::Word),
                _ => Err(crate::systypes::Status::Invalid),
            }
        }
    }

    pub enum GpdmaPriority {
        Low = 0,
        Medium = 1,
        High = 2,
        VeryHigh = 3,
    }

    impl TryFrom<u8> for GpdmaPriority {
        type Error = crate::systypes::Status;
        fn try_from(mode: u8) -> Result<GpdmaPriority, Self::Error> {
            match mode {
                0 => Ok(GpdmaPriority::Low),
                1 => Ok(GpdmaPriority::Medium),
                2 => Ok(GpdmaPriority::High),
                3 => Ok(GpdmaPriority::VeryHigh),
                _ => Err(crate::systypes::Status::Invalid),
            }
        }
    }

    /// DMA static configuration information
    ///
    /// # Usage
    ///
    /// This structure is delivered by the kernel into svc_exchange when
    /// calling successfully [`crate::syscall::dma_get_stream_info()`].
    ///
    /// The structure content correspond to the static build-time information
    /// as defined in the device-tree and do not require any DTS manipulation
    /// in user-space.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let dmacfg: dma_stream_cfg;
    /// match get_dma_stream_info(dmah) {
    ///    Status::Ok => (svc_exchange::copy_from(&dma_stream_cfg, mem::sizeof(dma_stream_cfg)))
    /// }
    /// ```
    ///
    #[repr(C)]
    #[derive(Debug, Copy, Clone)]
    pub struct GpdmaStreamConfig {
        pub channel: u16,
        pub stream: u16,
        pub controller: u16,
        pub transfer_type: u16,
        pub source: usize,
        pub dest: usize,
        pub transfer_len: usize,
        pub circular_source: bool,
        pub circular_dest: bool,
        pub interrupts: u8,
        pub is_triggered: bool,
        pub trigger: u8,
        pub priority: u8,
        pub transfer_mode: u8,
        pub src_beat_len: u8,
        pub dest_beat_len: u8,
    }

    // test that the Rust structure fields offset do match the corresponding C one,
    // as the kernel delivers in its ABI the C-defined structure
    #[test]
    fn test_layout_gpdma_stream_cfg() {
        const UNINIT: ::std::mem::MaybeUninit<GpdmaStreamConfig> =
            ::std::mem::MaybeUninit::uninit();
        let ptr = UNINIT.as_ptr();
        assert_eq!(
            ::std::mem::size_of::<GpdmaStreamConfig>(),
            48usize,
            concat!("Size of: ", stringify!(GpdmaStreamConfig))
        );
        assert_eq!(
            ::std::mem::align_of::<GpdmaStreamConfig>(),
            8usize,
            concat!("Alignment of ", stringify!(GpdmaStreamConfig))
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).channel) as usize - ptr as usize },
            0usize,
            concat!(
                "Offset of field: ",
                stringify!(GpdmaStreamConfig),
                "::",
                stringify!(channel)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).stream) as usize - ptr as usize },
            2usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(stream)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).controller) as usize - ptr as usize },
            4usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(controller)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).transfer_type) as usize - ptr as usize },
            6usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(transfer_type)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).source) as usize - ptr as usize },
            8usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(source)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).dest) as usize - ptr as usize },
            16usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(dest)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).transfer_len) as usize - ptr as usize },
            24usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(transfer_len)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).circular_source) as usize - ptr as usize },
            32usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(circular_source)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).circular_dest) as usize - ptr as usize },
            33usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(circular_dest)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).interrupts) as usize - ptr as usize },
            34usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(interrupts)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).is_triggered) as usize - ptr as usize },
            35usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(is_triggered)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).trigger) as usize - ptr as usize },
            36usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(trigger)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).priority) as usize - ptr as usize },
            37usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(priority)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).transfer_mode) as usize - ptr as usize },
            38usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(transfer_mode)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).src_beat_len) as usize - ptr as usize },
            39usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(src_beat_len)
            )
        );
        assert_eq!(
            unsafe { ::std::ptr::addr_of!((*ptr).dest_beat_len) as usize - ptr as usize },
            40usize,
            concat!(
                "Offset of field: ",
                stringify!(gpdma_stream_cfg),
                "::",
                stringify!(dest_beat_len)
            )
        );
    }

    pub enum GpdmaChanState {
        Idle = 1,
        Running = 2,
        Aborted = 3,
        Suspended = 4,
        TransmissionFailure = 5,
        ConfigurationFailure = 6,
        Overrun = 7,
        TransferComplete = 8,
        HalfTransfer = 9,
    }
}
