// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#[cfg(target_arch = "arm")]
#[macro_use]
pub mod arm_cortex_m;

#[cfg(target_arch = "riscv32")]
#[macro_use]
pub mod riscv32;
