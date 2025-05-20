// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

fn main() {
    // Link the C library for the STM32 basic timer
    cc::Build::new()
        .file("../../drivers/timer/stm32-basic-timer.c")
        .include("../../drivers/timer")
        .compile("stm32_basic_timer");
}
