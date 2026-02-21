// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

//! [![github]](https://github.com/camelot-os/sentry-kernel)&ensp;
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//!
//! <br>
//!
//! sentry_uapi is the user API library that delivers a full access to the Sentry kernel
//! interface.
//! This crate aim to be used by any Sentry-OS Rust application.
//!
//! -**Data types** — Sentry_uapi provices a complete set of data types and
//!  values that are required in order to properly exchange informations with the Sentry kernel.
//!  All the data types are stored in the [`mod@systypes`] public module.
//!
//! -**Sentry syscalls** — Syscall are defined in a two layers way. The bare syscalls
//!  are implemented in the [`mod@syscall`] module, while the upper, easy interface
//!  is out of the scope of this very crate, and written in the shield crate instead.

#![cfg_attr(
    not(all(target_arch = "x86_64", target_os = "linux")),
    no_std
)]

/// Support for std in POSIX mode, only for linux/x86_64 targets
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
extern crate std;

#[macro_use]
mod arch;

/// Sentry UAPI C export interface module
///
/// # Usage
///
/// This module should not be used in a full Rust application, while this is the lonely
/// accessible interface in C.
/// This allows a full Rust usage without extern C and thus unsafe calls when
/// writing Rust application with cargo
/// interface is used. Sentry kernel interactions should be, instead, made with
/// a upper interface such as shield.
///
pub mod ffi_c;

/// Sentry kernel exchange area manipulation primitives
///
/// # Usage
///
/// This module should not be used directly unless the [`mod@syscall`] module
/// interface is used. Sentry kernel interactions should be, instead, made with
/// an upper interface.
///
/// As the exchange area is a special userspace/kernelspace fixed size area
/// made in order to exchange data between userspace and kernelspace without
/// manipulating any pointer, this space has a particular meaning and usage, holding
/// any type of content as a 'retention area' before and after system calls.
/// This area is exclusive to the current job.
///
/// # About unsafe in this module
///
/// This module needs to interact with a single, static mutable area where both
/// kernel and job exchange data. As such, Rust consider any manipulation of this
/// area as unsafe due to potential multiple references to a static mutable space.
///
/// As Sentry kernel ensures that any job being executed has a single thread, no
/// race condition can happen due to the overall system design. As a consequence, even
/// if unsafe is used, there is no UB risk when manipulating the exchange area
/// based on the Operating System architecture.
///
mod exchange;

/// Sentry kernel low level syscall implementation
///
/// # Usage
///
/// This module is responsible for calling the kernel gate through the target
/// architecture supervisor access opcode, in interaction with the corresponding
/// arch backend.
///
/// There is no abstraction at this module's level and should not be used directly,
/// but instead with an upper interface such as shield
///
/// > **NOTE**: This module may not be kept public forever
//
#[cfg(not(all(target_arch = "x86_64", target_os = "linux")))]
pub mod syscall;

/// POSIX-based syscall implementation
///
/// # Usage
///
/// This module is responsible for making uapi functional in POSIX mode, by providing
/// a syscall implementation that is based on the POSIX API and thus only available
/// for linux/x86_64 targets.
///
//
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[path = "posix.rs"]
pub mod syscall;

/// Sentry kernelspace/userspace shared types and values
///
/// # Usage
///
/// This module holds all the Sentry kernel types and values required by all other modules
/// but also types that need to be used by upper layers in order to properly manipulate
/// Sentry's syscalls.
///
/// This module do not hold any function nor macro, but only all scalar and non-scalar
/// types for userspace/Sentry-kernel exchanges.
///
/// Some types are snake case based because of the C export. None the less,
/// they will be moved to standard Rust Caml case to stay conform to the
/// Rust guildelines
///
/// > **Note**: there is no bindgen nor cbindgen call in order to ensure FFI
/// > interface with the C language, to avoid any inter-languages naming and
/// > complexity (macros cases, static inline case and so on), meaning that
/// > the corresponding C types are defined in a dedicated include dir
///
pub mod systypes;

/// Copy a given generic type from the kernel exchange zone to the given mutable reference
pub use self::exchange::copy_from_kernel;

/// Copy a given generic type to the kernel exchange zone from the given eference
pub use self::exchange::copy_to_kernel;

/// Sentry exchangeable opaque trait, only defined for systypes defined types
///
/// This trait is declared in order to allow the attribute checking but is not
/// exported as no upper layer type needs to implement it
pub use self::exchange::SentryExchangeable;

/// Re-export Sentry uapi length fonction for Kani tests
pub use self::exchange::length;

#[cfg(not(all(target_arch = "x86_64", target_os = "linux")))]
mod panic;
