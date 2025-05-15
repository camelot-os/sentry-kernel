// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

mod test_ipc;
mod test_irq;
mod test_map;
mod test_random;
mod test_shm;
mod test_signal;
mod test_sleep;
mod test_yield;
mod test_cycles;

#[no_mangle]
pub extern "C" fn main() -> ! {
    test_ipc::test_ipc();
    test_irq::test_irq();
    test_map::test_map();
    test_random::test_random();
    test_signal::test_signal();
    test_shm::test_shm();
    test_sleep::test_sleep();
    test_yield::test_yield();
    test_dma::test_dma();
    test_cycles::test_cycles();
}

