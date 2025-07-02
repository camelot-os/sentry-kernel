// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

#[cfg(CONFIG_TEST_DEVICES)]
mod devices_dt;
#[cfg(CONFIG_TEST_DEVICES)]
mod devices_utils;
#[cfg(CONFIG_TEST_CYCLES)]
mod test_cycles;
#[cfg(CONFIG_TEST_DMA)]
mod test_dma;
#[cfg(CONFIG_TEST_IPC)]
mod test_ipc;
#[cfg(CONFIG_TEST_IRQ)]
mod test_irq;
mod test_log;
#[cfg(CONFIG_TEST_DEVICES)]
mod test_map;
#[cfg(CONFIG_TEST_RANDOM)]
mod test_random;
#[cfg(all(CONFIG_TEST_SHM,CONFIG_TEST_DEVICES))]
mod test_shm;
#[cfg(CONFIG_TEST_SIGNALS)]
mod test_signal;
#[cfg(CONFIG_TEST_SLEEP)]
mod test_sleep;
#[cfg(CONFIG_TEST_YIELD)]
mod test_yield;
#[cfg(CONFIG_TEST_GPIO)]
mod test_gpio;

// use kconfig;

#[unsafe(no_mangle)]
pub fn autotest() {
    // kconfig_import::import_dotconfig_from_script();

    #[cfg(CONFIG_TEST_IPC)]
    test_ipc::test_ipc();
    #[cfg(CONFIG_TEST_IRQ)]
    test_irq::test_irq();
    #[cfg(CONFIG_TEST_DEVICES)]
    test_map::test_map();
    #[cfg(CONFIG_TEST_RANDOM)]
    test_random::test_random();
    #[cfg(CONFIG_TEST_SIGNALS)]
    test_signal::test_signal();
    #[cfg(all(CONFIG_TEST_SHM,CONFIG_TEST_DEVICES))]
    test_shm::test_shm();
    #[cfg(CONFIG_TEST_SLEEP)]
    test_sleep::test_sleep();
    #[cfg(CONFIG_TEST_YIELD)]
    test_yield::test_yield();
    #[cfg(CONFIG_TEST_DMA)]
    test_dma::test_dma();
    #[cfg(CONFIG_TEST_CYCLES)]
    test_cycles::test_cycles();
    #[cfg(CONFIG_TEST_GPIO)]
    test_gpio::test_gpio();
}
