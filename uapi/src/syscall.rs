// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

use crate::exchange;
use crate::systypes::*;
#[cfg(not(target_arch = "x86_64"))]
use core::arch::asm;

/// Exits the current job
///
/// # Usage
///
/// This function immediately exit the current job instance, returning
/// the given status as job termination status code.
///
/// The status code is any 32 bit integer.
/// There is no Sentry-level semantic about the status code value. This
/// value is only used in order to call the `_finish(status)` function of the
/// current task so that it is possible to delivers differentiated
/// termination behavior depending on the returned status code. See
/// [Sentry concept](https://sentry-kernel.readthedocs.io/en/latest/concepts/initial.html#action-on-termination)
/// for more informations about task terminations.
///
/// > **NOTE**: This function never returns.
///
/// # Example
///
/// ```ignore
/// sentry_uapi::syscall::exit(42);
/// // unreachable
/// ```
///
#[inline(always)]
pub fn exit(status: i32) -> Status {
    syscall!(Syscall::Exit, status as u32).into()
}

/// Get global identifier for a given process label
///
/// # Usage
///
/// This syscall set the task handle that matches the given label in the
/// SVC_EXCHANGE area if the label is matched and is in the same domain as
/// the current task in the kernel task vector.
///
/// If no handle is found, the resulting status is Status::Invalid. If the
/// requested application is not in the same domain as the current one,
/// Status::Denied is returned. The SVC_EXCHANGE area is not set.
///
/// > **NOTE**: except without good reasons, do not use this syscall directly
///
/// # Example
///
/// ```ignore
/// match sentry_uapi::syscall::get_process_handle(tasklabel) {
///     Status::Ok => (),
///     any_err => return (any_err),
/// }
/// let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..4] };
/// let handle = u32::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
/// ```
///
#[inline(always)]
pub fn get_process_handle(process: TaskLabel) -> Status {
    syscall!(Syscall::GetProcessHandle, process).into()
}

/// Get global identifier for a given SHM label
///
/// # Usage
///
/// This syscall set the SHM handle that matches the given label in the
/// SVC_EXCHANGE area if the label matches a shared-memory that has been
/// declared in the device tree, and is owned or shared with the current task.
///
/// If label is not found or no accessible shared memory is found, the
/// resulting status is Status::Invalid. The SVC_EXCHANGE area is not set.
///
///  > **NOTE**: except without good reasons, do not use this syscall directly
///
/// # Example
///
/// ```ignore
/// match sentry_uapi::syscall::get_shm_handle(shmlabel) {
///     Status::Ok => (),
///     any_err => return (any_err),
/// }
/// let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..4] };
/// let handle = u32::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
/// ```
///
#[inline(always)]
pub fn get_shm_handle(shm: ShmLabel) -> Status {
    syscall!(Syscall::GetShmHandle, shm).into()
}

/// Get global identifier for a given DMA stream label
///
/// # Usage
///
/// This syscall set the MA stream handle that matches the given label in the
/// SVC_EXCHANGE area if the label matches a DMA stream that has been
/// declared in the device tree and is owned by the current task.
///
/// If label is not found or no accessible shared memory is found, the
/// resulting status is Status::Invalid. The SVC_EXCHANGE area is not set.
///
///  > **NOTE**: except without good reasons, do not use this syscall directly
///
/// # Example
///
/// ```ignore
/// match get_dma_stream_handle(streamlabel) {
///    Status::Ok => (),
///     any_err => return (any_err),
/// }
/// let exch_area = unsafe { &mut SVC_EXCHANGE_AREA[..4] };
/// let handle = u32::from_ne_bytes(exch_area.try_into().map_err(|_| Status::Invalid)?);
/// ```
///
#[inline(always)]
pub fn get_dma_stream_handle(stream: StreamLabel) -> Status {
    syscall!(Syscall::GetDmaStreamHandle, stream).into()
}

/// Release the processor before the end of the current quantum
///
/// # Usage
///
/// Allows triggering a schedule() even if not in the process's central blocking point.
/// This permits to preempt the current job even if the current quantum is reached.
/// This permits to ensure that when coming back from a yield call, the current
/// job quantum is full, giving a well-known time window in which the job will not
/// be preempted by another job.
///
/// Calling this syscall do not make the task uneligible, but instead push the task
/// bellow in the Sentry's scheduler queue. See [Sentry scheduler](https://sentry-kernel.readthedocs.io/en/latest/sw_architecture/schedulers.html#rrmq-scheduler)
/// documentation for more information.
///
/// This syscall never fails. This syscall preempt the current job.
///
/// There is no useful check of the syscall return code as it is always Status::Ok.
///
/// # Example
///
/// ```ignore
/// sentry_uapi::syscall::sched_yield();
/// ```
///
#[inline(always)]
pub fn sched_yield() -> Status {
    syscall!(Syscall::Yield).into()
}

/// Sleep for a given amount of time
///
/// # Usage
///
/// Allows to preempt and release the current job from the scheduler queue for a
/// given amount of time.
///
/// The requested sleeping method support multiple modes, based on the
/// [`SleepMode`]
///
///  - **deep sleeping** — Ensure that the task is sleeping for a minimum amount of
///    time, whatever happen.
///
///  - **shallow sleeping** — sleeps for a maximum duration, allowing job schedule
///    if an external event targets the task.
///
/// The sleep duration is based on the duration_ms input parameter.
/// See [`SleepDuration`] definition for various duration definitions.
///
/// This syscall never fails, but may return different Status code depending on the
/// awakening event.
/// If the job is awoken before the end of the required sleep duration, the
/// returned status is Status::Intr. If the job reaches the end of its
/// sleeping duration, the syscall returns Status::Timeout.
///
/// # Example
///
/// ```ignore
/// match sentry_uapi::syscall::sleep(SleepMode::Deep, D5ms) {
///    Status::Intr => (),
///    Status::Timeout => (),
/// }
/// ```
///
#[inline(always)]
pub fn sleep(duration_ms: SleepDuration, mode: SleepMode) -> Status {
    syscall!(Syscall::Sleep, u32::from(duration_ms), u32::from(mode)).into()
}

/// Start another task identified by its label
///
/// # Usage
///
/// This syscall allows a task with the CAP_SYS_PROCSTART capability
/// to start another task using its label.
///
/// Starting another task do not preempt the current job.
/// The newly started task is eligible and added to the scheduler queue.
///
/// If the current job do not own the capability, this syscall returns
/// Status::Denied. If the target task is already started, this syscall
/// returns Status::Invalid
///
/// # Example
///
/// ```ignore
/// match start(tsklabel) {
///    Status::Ok => (),
///    any_err => return(any_err),
/// }
/// ```
///
#[inline(always)]
pub fn start(process: TaskLabel) -> Status {
    syscall!(Syscall::Start, process).into()
}

///  Map a device in the caller's memory layout
///
/// # Usage
///
/// Maps a given device identified by its handle (see [`get_device_handle`]).
///
/// The memory mapping system is responsible for verifying that there is enough space
/// in the caller's memory layout, and if yes, do map, synchronously, the device area
/// in the caller's memory. The device is mapped read-write, so that the caller can
/// directly configure it.
///
/// Any mapped device can be unmapped (see [`unmap_dev`]).
///
/// This syscall returns Status::Ok if the device is successfully mapped by the kernel.
///
/// If the device handle is not owned by the caller or the caller do not own the
/// device's capability, the syscall returns Status::Denied
/// If the device handle is not found, or the device is already mapped, the syscall
/// returns Status::Invalid.
/// If the device can't be mapped (e.g. if the task memory layout is already full)
/// the syscall returns Status::Busy.
///
/// # Example
///
/// ```ignore
/// match map_dev(devh) {
///    Status::Ok => (),
///    Status::Busy => (unmap_other()),
///    any_err => return(any_err),
/// }
/// ```
///
#[inline(always)]
pub fn map_dev(dev: DeviceHandle) -> Status {
    syscall!(Syscall::MapDev, dev).into()
}

///  Map a shared memory in the caller's memory layout
///
/// # Usage
///
/// Maps a given shared identified by its handle (see [`get_shm_handle`]).
///
/// The memory mapping system is responsible for verifying that there is enough space
/// in the caller's memory layout, and if yes, do map, synchronously, the shared memory
/// in the caller's memory.
/// The memory access policy is based on the SHM policy defined for the caller through
/// the [`shm_set_credential`] syscall. The SHM mapping is synchronous.
///
/// Any shared memory can be unmapped (see [`unmap_shm`]).
///
/// This syscall returns Status::Ok if the device is successfully mapped by the kernel.
///
/// If the shared memory handle is not associated to the caller (neither own nor previously declared
/// as user), the syscall returns Status::Denied
/// If the shared memory handle is not found, or the shared memory is already mapped, the syscall
/// returns Status::Invalid.
/// If the shared memory can't be mapped (e.g. if the task memory layout is already full)
/// the syscall returns Status::Busy.
///
/// # Example
///
/// ```ignore
/// match map_shm(shmh) {
///    Status::Ok => (),
///    Status::Busy => (unmap_other()),
///    any_err => return(any_err),
/// }
/// ```
///
#[inline(always)]
pub fn map_shm(shm: ShmHandle) -> Status {
    syscall!(Syscall::MapShm, shm).into()
}

///  Unùap a previously mapped device
///
/// # Usage
///
/// Unmap a device that has been previously mapped by the caller, once no more
/// required. The device device is identified by its handle (see [`get_device_handle`]).
///
/// The memory mapping system is responsible for verifying that the device is already
/// mapped in the caller's memory layout. There is neither capability nor ownership check
/// as these checks are made at map time. Unmapping is synchronous.
///
/// An unmapped device can always be remapped later (see [`map_dev`]).
///
/// This syscall returns Status::Ok if the device is successfully unmapped by the kernel.
///
/// If the device is not already mapped by the caller, the syscall
/// returns Status::Invalid.
///
/// # Example
///
/// ```ignore
/// match unmap_dev(devh) {
///    Status::Ok => (),
///    any_err => return(any_err),
/// }
/// ```
///
#[inline(always)]
pub fn unmap_dev(dev: DeviceHandle) -> Status {
    syscall!(Syscall::UnmapDev, dev).into()
}

///  Unmap a previously mapped shared memory
///
/// # Usage
///
/// Unmap a shared memory that has been previously mapped by the caller, once no more
/// required. The shared memory is identified by its handle (see [`get_shm_handle`]).
///
/// The memory mapping system is responsible for verifying that the shared memory is already
/// mapped in the caller's memory layout. There is no ownership check
/// as these checks are made at map time. Unmapping is synchronous.
///
/// An unmapped shared memory can always be remapped later while credentials are
/// still valid for the caller (see [`map_shm`] and [`shm_set_credential`]).
///
/// This syscall returns Status::Ok if the shared memory is successfully unmapped by the kernel.
/// If the shared memory is not already mapped by the caller, the syscall returns Status::Invalid.
///
/// # Example
///
/// ```ignore
/// match unmap_shm(devh) {
///    Status::Ok => (),
///    any_err => return(any_err),
/// }
/// ```
///
#[inline(always)]
pub fn unmap_shm(shm: ShmHandle) -> Status {
    syscall!(Syscall::UnmapShm, shm).into()
}

///  Set the credentials associated to a shared memory
///
/// # Usage
///
/// Specify the credentials and declare usership for a given, owned, shared memory.
/// a shared memory hold two instances of credentials. One for the shared memory
/// owner and one for the samed memory user.
/// This syscall provides a credentials configuration interface for both instances,
/// only for the shared memory owner.
///
/// Credentials are based on a bitfield model, as defined in [`SHMPermission`].
/// Setting credentials is synchronous. There is no specific capability associated
/// to this interface as the shared memory ownership is considered instead.
///
/// Setting shared memory credential is **required** before any usage of the shared memory,
/// meaning that even the owner can't manipulate a shared memory while the credentials have
/// not been set at least one.
///
/// When setting credentials for another task, the shared memory is synchronously ready to
/// be used by the other task without any other required action. The shared memory handle
/// exchange with the other task is out of the current syscall and needs to be made through
/// a task-specific, independent, communication channel.
///
/// a shared memory credentials can't be set for a given target (owner or user) while this
/// very target has mapped the shared memory. This check is **not done** if the shared memory
/// is used without mapping (e.g. if the target uses DMA stream(s) that target this shared
/// memory without having it mapped). Such a behavior control is instead delegated to the integrator
/// through the analysis of the device tree configuration, including the shared memory declared
/// owner and the declared shared memories for which the `dma-pool` attribute is set.
///
/// This syscall returns Status::Invalid if the shared memory handle is out of the caller's scope
/// (if the caller is neither an owner or a user of the shared memory).
/// This syscall returns Status::Invalid if any of the parameter is malformated or if the
/// target task handle is not found.
/// This syscall returns Status::Denied if the caller is a user of the shared memory, but do not
/// own it.
/// This syscall return Status::Busy if the target of the credential setting as mapped the
/// shared memory.
/// This syscall returns Status::Ok if the credentials are properly set.
///
/// # Example
///
/// ```ignore
/// match shm_set_credential(shmh, myhandle, SHMPermission::Map | SHMPermission::Write) {
///    Status::Ok => (),
///    any_err => return(any_err),
/// }
/// ```
///
/// # See also
///
/// Shared memory related syscalls:
/// [`get_shm_handle`], [`map_shm`], [`unmap_shm`] and [`shm_get_infos`].
///
#[inline(always)]
pub fn shm_set_credential(shm: ShmHandle, id: TaskHandle, shm_perm: u32) -> Status {
    syscall!(Syscall::SHMSetCredential, shm, id, shm_perm).into()
}

/// Send events to another job identified by its handle
///
/// # description
///
/// This syscall emit a short message through the SVC Exchange memory that target
/// another job identified by its handle.
///
/// The IPC message content must be stored 'as is' in the SVC exchange memory before
/// calling this syscall. The message length must be shorter than the SVC Exchange
/// area.
///
/// `send_ipc()` is a blocking syscall. The current job is preempted and will
/// be eligible again only if:
///
///    * the target job reads the IPC content using [`wait_for_event`]
///    * the target job terminates
///
/// This syscall synchronously returns `Status::Invalid` If the target job handle
/// is not found.
/// This syscall synchronously returns `Status::Invalid` if the specified message len
/// is bigger than
/// This syscall returns `Status::Intr` if the target terminates while the IPC
/// message is not yet read.
/// This syscall returns `Status::Ok` once the target as read the IPC message.
///
/// **Note**: This syscall do not clear the SVC Exchange area.
///
/// There is no timeout notion in IPC emission, meaning that a given job can stay
/// in a blocking state forever while the target neither read the emitted IPC nor
/// terminates.
///
/// # examples
///
/// ```ignore
/// uapi::send_ipc(TargetTaskh, IpcLen)?continue_here;
/// ```
///
#[inline(always)]
pub fn send_ipc(target: TaskHandle, length: u8) -> Status {
    syscall!(Syscall::SendIPC, target, length as u32).into()
}

/// Send signal to another job identified by its handle
///
/// # description
///
/// This syscall emit a signal that target another job identified by its handle.
///
/// A signal is not data, and as such there is no data copy between tasks.
/// Signals are asynchronous events. This syscall is not a blocking syscall, the
/// target has not received the signal when returning from this syscall.
///
/// The signal list is compile-time fixed and can't be increased at runtime.
/// The signal definitions and proper associated usage is listed in [`Signal`].
///
/// As this syscall is fully asynchronous, there is no way to be informed that
/// the target has read the signal.
///
/// This syscall returns `Status::Invalid` If the target job handle
/// is not found.
/// This syscall returns `Status::Invalid` if the signal identifier do not exist.
/// If a task emit a signal while the target hasn't read the previous one from
/// the same source, the syscall returns `Status::Busy`.
///
/// This syscall returns `Status::Ok` once the signal is delivered into the target
/// input queue.
///
/// **Note**: The signal input queue is per-peer with a depth of 1, meaning that there
/// is no impact between tasks if multiple tasks send signals to the same target.
///
///
/// # examples
///
/// ```ignore
/// send_signal(TargetTaskh, Signal::Pipe)?continue_here;
/// ```
///
#[inline(always)]
pub fn send_signal(resource: u32, signal_type: Signal) -> Status {
    syscall!(Syscall::SendSignal, resource, signal_type as u32).into()
}

#[allow(clippy::tabs_in_doc_comments)]
/// Get the value of a given GPIO for a device identified by its handle
///
/// # description
///
/// This syscall allows to get back the value of a GPIO identifier associated
/// to the corresponding pinmux declared in the device tree.
///
/// Considering the following device tree content:
///
/// ```dts
/// &i2c1 {
///     status = "okay";
///	    sentry,owner = <0xC001F001>;
///     pinctrl-0 = <&i2c1_sda>;
/// }
///
/// i2c1_sda: i2c_sda_pb9  {
///	    label = "sda";
///     pinmux = <&gpiob 9 STM32_DT_PIN_MODE_ALTFUNC(4)>;
///     pincfg = <STM32_OTYPER_OPEN_DRAIN \
///               STM32_OSPEEDR_VERY_HIGH_SPEED \
///               STM32_PUPDR_PULL_UP>;
///    };
/// ```
/// The task-level i2c1 table generated would then hold a one entry
/// vector with the Sda index named identified explicitly, targeting
/// the lonely vector cell.
///
/// This identifier can be used as-is for the io input value.
///
/// This syscall returns Status::Invalid if the io does not exist for the
/// given device handle or if the device handle itself is invalid or not owned.
/// This syscall returns Status::Ok if the GPIO has been read, and the GPIO
/// value can be acceded in the SVC_Exchange area.
///
/// # Example
///
/// ```ignore
/// gpio_get(devh, Sda);
/// ```
///
#[inline(always)]
pub fn gpio_get(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioGet, resource, io as u32).into()
}

/// Set the value of a given GPIO for a device identified by its handle
///
/// # description
///
/// This syscall allows to get back the value of a GPIO identifier associated
/// to the corresponding pinmux declared in the device tree.
///
/// Its behavior is similar to [`gpio_get`]. the value set is a classical
/// boolean value, used in order to set high or low the value of the GPIO pin.
///
/// If the given GPIO is in input mode, the syscall returns `Status::Badstate`.
///
/// Except this specific behavior, this syscall behave the same way as [`gpio_get`].
///
#[inline(always)]
pub fn gpio_set(resource: u32, io: u8, val: bool) -> Status {
    syscall!(Syscall::GpioSet, resource, io as u32, val as u32).into()
}

/// Reset the value of a given GPIO for a device identified by its handle
///
/// # description
///
/// This syscall allows to get back the value of a GPIO identifier associated
/// to the corresponding pinmux declared in the device tree.
///
/// Its behavior is similar to [`gpio_set`]. the value set is reset to low
/// level, behave n the same way as `gpio_set()` with `value` parameter set
/// to `false`.
///
#[inline(always)]
pub fn gpio_reset(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioReset, resource, io as u32).into()
}

/// Toggle the value of a given GPIO for a device identified by its handle
///
/// # description
///
/// This syscall invert the GPIO pin value of a GPIO identifier associated
/// to the corresponding pinmux declared in the device tree.
///
/// Its behavior is similar to [`gpio_reset`], except that the new GPIO pin
/// value is based on the inversion of its current value.
///
#[inline(always)]
pub fn gpio_toggle(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioToggle, resource, io as u32).into()
}

/// Configure a given GPIO for a device identified by its handle
///
/// # description
///
/// This syscall configures the GPIO using the corresponding pinmux settings set
/// in the device-tree. See [`gpio_get`] for device-tree related description.
///
/// The return values are similar to [`gpio_get`]. The GPIO is synchronously
/// set according to the corresponding pinmux definition.
///
#[inline(always)]
pub fn gpio_configure(resource: u32, io: u8) -> Status {
    syscall!(Syscall::GpioConfigure, resource, io as u32).into()
}

/// Get global identifier for a given device label
///
/// # Usage
///
/// This syscall set the device handle that matches the given label in the
/// SVC_EXCHANGE area if the label is found in the kernel declared device list.
///
/// If no handle is found, the resulting status is Status::Invalid. If the
/// requested device not in own by the caller, Status::Denied is returned.
/// In these cases, the SVC_EXCHANGE area is not set.
///
///
#[inline(always)]
pub fn get_device_handle(devlabel: u8) -> Status {
    syscall!(Syscall::GetDeviceHandle, devlabel as u32).into()
}

/// acknowledge at interrupt controller level the given interrupt
#[inline(always)]
pub fn irq_acknowledge(irq: u16) -> Status {
    syscall!(Syscall::IrqAcknowledge, irq as u32).into()
}

/// enable (unmask) at interrupt controller level the given interrupt
#[inline(always)]
pub fn irq_enable(irq: u16) -> Status {
    syscall!(Syscall::IrqEnable, irq as u32).into()
}

/// disable (mask) at interrupt controller level the given interrupt
#[inline(always)]
pub fn irq_disable(irq: u16) -> Status {
    syscall!(Syscall::IrqDisable, irq as u32).into()
}

/// Wait for input event. Single active blocking syscall.
///
/// This syscall holds the current thread as long as none of the event requested
/// in the given event mask is received.
///
/// The event source (a device for an interrupt, a PID for an IPC or signal) can be set.
/// Setting the source to 0 means that any source is allowed.
///
/// If received, event information is set in the task SVC data
/// structure and the function returns `Status::Ok`.
///
/// This function must be the single blocking point of the function (excepting
/// sleep() case)
///
/// NOTE: The timeout is kept i32 by now due to C FFI. Usage of enumerate is not
/// easy as, at the end, the value is set to a HW register... which is a u32, to be
/// transferred to the kernel corresponding gate.
///
#[inline(always)]
pub fn wait_for_event(mask: u8, timeout: i32) -> Status {
    let timeout = u32::try_from(timeout);
    match timeout {
        Ok(_) => (),
        Err(_) => return Status::Invalid,
    };
    match syscall!(Syscall::WaitForEvent, u32::from(mask), timeout.unwrap()).into() {
        Status::Intr => syscall!(Syscall::WaitForEvent, u32::from(mask), timeout.unwrap()).into(),
        any => any,
    }
}

/// Configure the CPU's sleep behaviour.
///
/// The `mode` parameters toggles between the two traditional wake-up
/// modes for ARM CPUs:
/// - wait for interrupt (`wfi`)
/// - wait for event (`wfe`)
///
/// it also accepts two other mode values that enable or prevent the
/// CPU from sleeping.
#[inline(always)]
pub fn pm_manage(mode: CPUSleep) -> Status {
    syscall!(Syscall::PmManage, u32::from(mode)).into()
}

/// Send a SIGALRM signal to the task after `timeout_ms` milliseconds.
#[inline(always)]
pub fn alarm(timeout_ms: u32, flag: AlarmFlag) -> Status {
    syscall!(Syscall::Alarm, timeout_ms, u32::from(flag)).into()
}

/// Send a message from the current task's 'svc_exchange area' through
/// the UART.
#[inline(always)]
pub fn log(length: usize) -> Status {
    if length > exchange::length() {
        Status::Invalid
    } else {
        syscall!(Syscall::Log, length as u32).into()
    }
}

/// Get random seed from the Sentry kernel RNG backend
///
/// # Usage
///
/// The random seed received is 32 bits length. If the caller needs to
/// forge a longer seeds without using an application hosted derivation, the
/// syscall need to be called multiple-time.
///
/// This syscall requires the caller to hold the CAP_CRY_KRNG capability.
/// Without this capability, Status::Denied is returned.
///
/// The syscall may fail if the kernel RNG source fails to properly delivers
/// a FIPS compliant random value. In that case, the syscall returns
/// Status::Critical.
///
/// The generated seed is delivered through the SVC_EXCHANGE zone.
///
/// # Example
///
/// ```ignore
/// match (get_random()) {
///     Status::Ok => (),
///     any_err => return(any_err),
/// };
/// ```
///
#[inline(always)]
pub fn get_random() -> Status {
    syscall!(Syscall::GetRandom).into()
}

/// Get back the elapsed time since startup, in various units
///
/// # Usage
///
/// The kernel store the elapsed time since its startup so that it is possible
/// to get basic time measurement, being from startup or between two call to
/// this API, in various format.
///
/// The precision required is passed in the unit argument, as defined in the
/// [`Precision`] type.
///
/// Whatever the precision is, the returned value is always encoded as `u64`.
///
/// While [`Precision::Milliseconds`] and [`Precision::Microseconds`] do not
/// require specific capability, [`Precision::Nanoseconds`] and [`Precision::Cycle`]
/// require the CAP_TIM_HP_CHRONO capability. This avoid any hability to
/// get high precision measurements that may leed to side channel analysis on
/// another task's behavior without having the corresponding capability.
///
/// Most of the time, this capability is not required.
///
/// This syscall returns the value in the SVC_EXCHANGE area, where it needs to
/// be read afterward.
///
#[inline(always)]
pub fn get_cycle(precision: Precision) -> Status {
    syscall!(Syscall::GetCycle, precision as u32).into()
}

/// Set a given explicit clock config
///
/// Required for complex devices that need to make clock configuration vary.
/// Requires the CAP_SYS_POWER capability
///
/// - TODO: using dts instead
/// - TODO: update documentation when moving to PM-related work
#[inline(always)]
pub fn pm_set_clock(clk_reg: u32, clkmsk: u32, val: u32) -> Status {
    syscall!(Syscall::PmSetClock, clk_reg, clkmsk, val).into()
}

/// start a DMA stream
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_start_stream(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaStartStream, dmah).into()
}

/// suspend a DMA stream
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_suspend_stream(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaSuspendStream, dmah).into()
}

/// get the status of a given DMA stream
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_get_stream_status(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaGetStreamStatus, dmah).into()
}

/// get the static information of a given DMA stream
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn shm_get_infos(shm: ShmHandle) -> Status {
    syscall!(Syscall::ShmGetInfos, shm).into()
}

/// assign a DMA stream to its corresponding hardware channel
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_assign_stream(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaAssignStream, dmah).into()
}

/// unassign a DMA stream from its corresponding hardware channel
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_unassign_stream(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaUnassignStream, dmah).into()
}

/// get a DMA stream static (dts-related) information from the kernel, as a
/// structured data through SVC_Exchange
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_get_stream_info(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaGetStreamInfo, dmah).into()
}

/// resume a DMA stream
///
/// TODO: with complete DMA support
#[inline(always)]
pub fn dma_resume_stream(dmah: StreamHandle) -> Status {
    syscall!(Syscall::DmaResumeStream, dmah).into()
}

/// Set (enable) given capability for autotest
/// Only autotest has the userspace knowledge of the capabilities effective values
#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[inline(always)]
pub fn autotest_set_capa(capability: u32) -> Status {
    syscall!(Syscall::AutotestSetCapa, capability).into()
}

/// Clear (disable) given capability for autotest
/// Only autotest has the userspace knowledge of the capabilities effective values
#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[inline(always)]
pub fn autotest_clear_capa(capability: u32) -> Status {
    syscall!(Syscall::AutotestClearCapa, capability).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syscall_enum() {
        for syscall_num in 0..32 {
            match Syscall::try_from(syscall_num) {
                Ok(sysn) => {
                    assert_eq!(sysn as u8, syscall_num); // ensure roundtrip loops
                }
                Err(_) => (),
            }
        }
    }

    #[test]
    fn basic_sleep() {
        assert_eq!(sleep(SleepDuration::D1ms, SleepMode::Shallow), Status::Ok);
    }

    #[test]
    fn basic_start() {
        assert_eq!(start(0), Status::Ok);
    }

    #[test]
    fn basic_yield() {
        assert_eq!(sched_yield(), Status::Ok);
    }

    #[test]
    fn basic_exit() {
        assert_eq!(exit(1), Status::Ok);
    }

    #[test]
    fn invalid_status() {
        assert_eq!(exit(0xaaaa), Status::Ok);
    }
}
