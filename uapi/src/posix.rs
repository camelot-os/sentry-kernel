// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

///
/// This module provides a POSIX-compatible implementation of the Sentry kernel
/// interface for Linux/x86_64 targets.
/// It serves as a compatibility layer, allowing applications to behave as if
/// they were interacting with the Sentry kernel, but  using standard
/// POSIX system calls and conventions.
/// This implementation is intended for use in environments where the Sentry kernel
/// is not available, such as during development or testing on a standard Linux system.
///
/// In order to support multi-tasking and inter-process communication (IPC) in a POSIX environment,
/// this module will interact with a local GNU/Linux server that simulates the Sentry kernel's behavior.
/// This server will handle the necessary system calls and manage the state of the simulated kernel,
/// allowing applications to communicate with external objects such as devices, shared memory,
/// and other task.
/// This server will be written as a separate component in this repository, in the tools directory.
/// Interactions with this server will be made through a local socket, and the protocol will be defined
/// in the documentation of the server itself, as well as in the documentation of this module.
///
/// Each Except for local-only syscalls such as `sched_yield` or `sys_exit`, all the syscalls
/// will behave as a proxy to the server, forwarding the syscall number and arguments to the
/// server and returning the server's response as the syscall result.
///

use crate::systypes::*;
use std::sync::OnceLock;
use tonic::codegen::http::uri::PathAndQuery;
use tonic::transport::Endpoint;
use tonic::{Request, Status as GrpcStatus};

const DEFAULT_EMULATOR_HOST: &str = "127.0.0.1";
const DEFAULT_EMULATOR_PORT: u16 = 44044;
const DEFAULT_APP_LABEL: u32 = 0;

static GRPC_RUNTIME: OnceLock<Option<tokio::runtime::Runtime>> = OnceLock::new();
static APP_LABEL: OnceLock<u32> = OnceLock::new();

#[derive(Clone, PartialEq, ::prost::Message)]
struct DispatchRequest {
    #[prost(string, tag = "1")]
    syscall: String,
    #[prost(sint64, repeated, tag = "2")]
    args: std::vec::Vec<i64>,
    #[prost(uint32, tag = "3")]
    label: u32,
    #[prost(bytes = "vec", tag = "4")]
    payload: std::vec::Vec<u8>,
}

#[derive(Clone, PartialEq, ::prost::Message)]
struct DispatchResponse {
    #[prost(sint32, tag = "1")]
    status: i32,
    #[prost(string, tag = "2")]
    detail: std::string::String,
    #[prost(bytes = "vec", tag = "3")]
    payload: std::vec::Vec<u8>,
}

fn grpc_runtime() -> Option<&'static tokio::runtime::Runtime> {
    GRPC_RUNTIME
        .get_or_init(|| {
            tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .ok()
        })
        .as_ref()
}

fn emulator_uri() -> std::string::String {
    let host = std::env::var("SENTRY_EMULATOR_HOST")
        .ok()
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| DEFAULT_EMULATOR_HOST.to_string());
    let port = std::env::var("SENTRY_EMULATOR_PORT")
        .ok()
        .and_then(|value| value.parse::<u16>().ok())
        .unwrap_or(DEFAULT_EMULATOR_PORT);
    format!("http://{host}:{port}")
}

fn app_label() -> u32 {
    *APP_LABEL.get_or_init(|| {
        std::env::var("SENTRY_APP_LABEL")
            .ok()
            .and_then(|value| value.parse::<u32>().ok())
            .unwrap_or(DEFAULT_APP_LABEL)
    })
}

fn status_from_i32(raw_status: i32) -> Status {
    match raw_status {
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
        _ => Status::Invalid,
    }
}

async fn grpc_dispatch(request: DispatchRequest) -> Result<DispatchResponse, GrpcStatus> {
    let endpoint = Endpoint::from_shared(emulator_uri())
        .map_err(|_| GrpcStatus::unavailable("invalid endpoint"))?;
    let channel = endpoint
        .connect()
        .await
        .map_err(|_| GrpcStatus::unavailable("cannot connect to emulator"))?;

    let mut client = tonic::client::Grpc::new(channel);
    client
        .ready()
        .await
        .map_err(|_| GrpcStatus::unavailable("emulator client not ready"))?;
    let codec = tonic::codec::ProstCodec::default();
    let path = PathAndQuery::from_static("/camelot.sentry.emulator.Emulator/Dispatch");
    let response = client.unary(Request::new(request), path, codec).await?;
    Ok(response.into_inner())
}

fn dispatch_with_payload(
    syscall: &str,
    args: &[i128],
    payload: &[u8],
) -> Result<DispatchResponse, Status> {
    let grpc_args = args
        .iter()
        .map(|value| i64::try_from(*value).ok())
        .collect::<Option<std::vec::Vec<i64>>>();

    let Some(grpc_args) = grpc_args else {
        return Err(Status::Invalid);
    };

    let request = DispatchRequest {
        syscall: syscall.to_string(),
        args: grpc_args,
        label: app_label(),
        payload: payload.to_vec(),
    };

    let Some(runtime) = grpc_runtime() else {
        return Err(Status::NoEntity);
    };

    match runtime.block_on(grpc_dispatch(request)) {
        Ok(response) => Ok(response),
        Err(_) => Err(Status::NoEntity),
    }
}

fn forward_syscall(syscall: &str, args: &[i128]) -> Status {
    match dispatch_with_payload(syscall, args, &[]) {
        Ok(response) => status_from_i32(response.status),
        Err(status) => status,
    }
}

pub(crate) fn exchange_to_daemon(data: &[u8]) -> Status {
    match dispatch_with_payload("exchange_to_kernel", &[], data) {
        Ok(response) => status_from_i32(response.status),
        Err(status) => status,
    }
}

pub(crate) fn exchange_from_daemon(data: &mut [u8]) -> Status {
    match dispatch_with_payload("exchange_from_kernel", &[], &[]) {
        Ok(response) => {
            let status = status_from_i32(response.status);
            if status != Status::Ok {
                return status;
            }

            let copy_len = core::cmp::min(data.len(), response.payload.len());
            data[..copy_len].copy_from_slice(&response.payload[..copy_len]);
            Status::Ok
        }
        Err(status) => status,
    }
}


#[inline(always)]
pub fn exit(status: i32) -> Status {
    let _ = forward_syscall("exit", &[status as i128]);
    std::process::exit(status);
}

#[inline(always)]
pub fn sleep(_duration_ms: SleepDuration, _mode: SleepMode) -> Status {
    match _duration_ms {
        SleepDuration::D1ms => {
            std::thread::sleep(std::time::Duration::from_millis(1));
            Status::Ok
        }
        SleepDuration::D2ms => {
            std::thread::sleep(std::time::Duration::from_millis(2));
            Status::Ok
        }
        SleepDuration::D5ms => {
            std::thread::sleep(std::time::Duration::from_millis(5));
            Status::Ok
        }
        SleepDuration::D10ms => {
            std::thread::sleep(std::time::Duration::from_millis(10));
            Status::Ok
        }
        SleepDuration::D20ms => {
            std::thread::sleep(std::time::Duration::from_millis(20));
            Status::Ok
        }
        SleepDuration::D50ms => {
            std::thread::sleep(std::time::Duration::from_millis(50));
            Status::Ok
        }
        SleepDuration::ArbitraryMs(ms) => {
            std::thread::sleep(std::time::Duration::from_millis(ms as u64));
            Status::Ok
        }
    }
}

#[inline(always)]
pub fn sched_yield() -> Status {
    std::thread::yield_now();
    Status::Ok
}

#[inline(always)]
pub fn get_process_handle(label: TaskLabel) -> Status {
    forward_syscall("get_process_handle", &[label as i128])
}

#[inline(always)]
pub fn send_ipc(target: TaskHandle, length: u8) -> Status {
    forward_syscall("send_ipc", &[target as i128, length as i128])
}
#[inline(always)]
pub fn wait_for_event(mask: u8, timeout: i32) -> Status {
    forward_syscall("wait_for_event", &[mask as i128, timeout as i128])
}

#[inline(always)]
pub fn map_dev(handle: DeviceHandle) -> Status {
    forward_syscall("map_dev", &[handle as i128])
}

#[inline(always)]
pub fn unmap_dev(handle: DeviceHandle) -> Status {
    forward_syscall("unmap_dev", &[handle as i128])
}

#[inline(always)]
pub fn get_shm_handle(shm: ShmLabel) -> Status {
    forward_syscall("get_shm_handle", &[shm as i128])
}

#[inline(always)]
pub fn get_device_handle(devlabel: u32) -> Status {
    forward_syscall("get_device_handle", &[devlabel as i128])
}

#[inline(always)]
pub fn get_dma_stream_handle(stream: StreamLabel) -> Status {
    forward_syscall("get_dma_stream_handle", &[stream as i128])
}

#[inline(always)]
pub fn start(process: TaskLabel) -> Status {
    forward_syscall("start", &[process as i128])
}

#[inline(always)]
pub fn map_shm(shm: ShmHandle) -> Status {
    forward_syscall("map_shm", &[shm as i128])
}

#[inline(always)]
pub fn unmap_shm(shm: ShmHandle) -> Status {
    forward_syscall("unmap_shm", &[shm as i128])
}

#[inline(always)]
pub fn shm_set_credential(
    shm: ShmHandle,
    id: TaskHandle,
    shm_perm: u32,
) -> Status {
    forward_syscall(
        "shm_set_credential",
        &[shm as i128, id as i128, shm_perm as i128],
    )
}

#[inline(always)]
pub fn send_signal(target: u32, sig: Signal) -> Status {
    forward_syscall("send_signal", &[target as i128, sig as i128])
}

#[inline(always)]
pub fn gpio_get(resource: u32, io: u8) -> Status {
    forward_syscall("gpio_get", &[resource as i128, io as i128])
}

#[inline(always)]
pub fn gpio_set(resource: u32, io: u8, val: bool) -> Status {
    forward_syscall(
        "gpio_set",
        &[resource as i128, io as i128, i128::from(val as u8)],
    )
}

#[inline(always)]
pub fn gpio_reset(resource: u32, io: u8) -> Status {
    forward_syscall("gpio_reset", &[resource as i128, io as i128])
}

#[inline(always)]
pub fn gpio_toggle(resource: u32, io: u8) -> Status {
    forward_syscall("gpio_toggle", &[resource as i128, io as i128])
}

#[inline(always)]
pub fn gpio_configure(resource: u32, io: u8) -> Status {
    forward_syscall("gpio_configure", &[resource as i128, io as i128])
}

#[inline(always)]
pub fn irq_acknowledge(irq: u16) -> Status {
    forward_syscall("irq_acknowledge", &[irq as i128])
}

#[inline(always)]
pub fn irq_enable(irq: u16) -> Status {
    forward_syscall("irq_enable", &[irq as i128])
}

#[inline(always)]
pub fn irq_disable(irq: u16) -> Status {
    forward_syscall("irq_disable", &[irq as i128])
}

#[inline(always)]
pub fn pm_manage(mode: CPUSleep) -> Status {
    forward_syscall("pm_manage", &[u32::from(mode) as i128])
}

#[inline(always)]
pub fn alarm(timeout_ms: u32, flag: AlarmFlag) -> Status {
    forward_syscall("alarm", &[timeout_ms as i128, u32::from(flag) as i128])
}

#[inline(always)]
pub fn log(_length: usize) -> Status {
    forward_syscall("log", &[_length as i128])
}

#[inline(always)]
pub fn get_random() -> Status {
    forward_syscall("get_random", &[])
}

#[inline(always)]
pub fn get_cycle(precision: Precision) -> Status {
    forward_syscall("get_cycle", &[precision as i128])
}

#[inline(always)]
pub fn pm_set_clock(clk_reg: u32, clkmsk: u32, val: u32) -> Status {
    forward_syscall(
        "pm_set_clock",
        &[clk_reg as i128, clkmsk as i128, val as i128],
    )
}

#[inline(always)]
pub fn dma_start_stream(dmah: StreamHandle) -> Status {
    forward_syscall("dma_start_stream", &[dmah as i128])
}

#[inline(always)]
pub fn dma_suspend_stream(dmah: StreamHandle) -> Status {
    forward_syscall("dma_suspend_stream", &[dmah as i128])
}

#[inline(always)]
pub fn dma_get_stream_status(dmah: StreamHandle) -> Status {
    forward_syscall("dma_get_stream_status", &[dmah as i128])
}

#[inline(always)]
pub fn shm_get_infos(shm: ShmHandle) -> Status {
    forward_syscall("shm_get_infos", &[shm as i128])
}

#[inline(always)]
pub fn dma_assign_stream(dmah: StreamHandle) -> Status {
    forward_syscall("dma_assign_stream", &[dmah as i128])
}

#[inline(always)]
pub fn dma_unassign_stream(dmah: StreamHandle) -> Status {
    forward_syscall("dma_unassign_stream", &[dmah as i128])
}

#[inline(always)]
pub fn dma_get_stream_info(dmah: StreamHandle) -> Status {
    forward_syscall("dma_get_stream_info", &[dmah as i128])
}

#[inline(always)]
pub fn dma_resume_stream(dmah: StreamHandle) -> Status {
    forward_syscall("dma_resume_stream", &[dmah as i128])
}

// Autotest only
#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[inline(always)]
pub fn autotest_set_capa(_capa: u32) -> Status {
    forward_syscall("autotest_set_capa", &[_capa as i128])
}

#[cfg(CONFIG_BUILD_TARGET_AUTOTEST)]
#[inline(always)]
pub fn autotest_clear_capa(_capa: u32) -> Status {
    forward_syscall("autotest_clear_capa", &[_capa as i128])
}

#[inline(always)]
pub fn unsupported() -> Status {
    forward_syscall("unsupported", &[])
}
