// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

pub mod log;

#[cfg(CONFIG_TEST_DEVICES)]
#[cfg(CONFIG_TEST_GPIO)]
mod devices_dt;
#[cfg(CONFIG_TEST_DEVICES)]
#[cfg(CONFIG_TEST_GPIO)]
mod devices_utils;
#[cfg(CONFIG_TEST_GPIO)]
pub mod test_gpio;
#[cfg(CONFIG_TEST_RANDOM)]
pub mod test_random;
#[cfg(CONFIG_TEST_SIGNALS)]
pub mod test_signal;
#[cfg(CONFIG_TEST_SLEEP)]
pub mod test_sleep;
#[cfg(CONFIG_TEST_YIELD)]
pub mod test_yield;
#[cfg(CONFIG_TEST_CYCLES)]
pub mod test_cycles;
#[cfg(CONFIG_TEST_IPC)]
pub mod test_ipc;
#[cfg(CONFIG_TEST_HANDLES)]
pub mod test_gethandle;
#[cfg(CONFIG_TEST_SHM)]
pub mod test_shm;
#[cfg(CONFIG_TEST_DEVICES)]
pub mod test_map;
#[cfg(CONFIG_TEST_DMA)]
pub mod test_dma;
