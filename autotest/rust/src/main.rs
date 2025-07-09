// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

mod print;
mod tests;

extern crate sentry_uapi;

use sentry_uapi::syscall;

///  Canari variable, as defined in LLVM & GCC compiler documentation, in order to
///  be manipulated each time a new frame is added on stack
#[unsafe(no_mangle)]
#[used]
static mut __stack_chk_guard: u32 = 0;

// autotest entrypoint
// defined as entrypoint in linkerscript
// sentry kernel will retrieve memory location of such a symbol to forge dedicated
// autotest task metadata.
#[unsafe(no_mangle)]
pub extern "C" fn autotest(_thread_id: u32, seed: u32) -> ! {
    unsafe { __stack_chk_guard = seed; }

    let welcommsg: &str = "hello this is autotest Rust !\n";
    let testmsg: &str = "starting test suite...\n";

    println!("{}", welcommsg);
    println!("{}", testmsg);
    println!("AUTOTEST START");

    #[cfg(CONFIG_TEST_HANDLES)]
    tests::test_gethandle::run();
    #[cfg(CONFIG_TEST_RANDOM)]
    tests::test_random::run();
    #[cfg(CONFIG_TEST_SIGNALS)]
    tests::test_signal::run();
    #[cfg(CONFIG_TEST_SLEEP)]
    tests::test_sleep::run();
    #[cfg(CONFIG_TEST_YIELD)]
    tests::test_yield::run();
    #[cfg(CONFIG_TEST_CYCLES)]
    tests::test_cycles::run();
    #[cfg(CONFIG_TEST_IPC)]
    tests::test_ipc::run();
    #[cfg(CONFIG_TEST_GPIO)]
    tests::test_gpio::run();
    #[cfg(CONFIG_TEST_SHM)]
    tests::test_shm::run();
    #[cfg(CONFIG_TEST_DEVICES)]
    tests::test_map::run();
    #[cfg(CONFIG_TEST_DMA)]
    tests::test_dma::run();

    syscall::exit(0);
    panic!();
}
