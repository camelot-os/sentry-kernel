// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-FileCopyrightText: 2025 H2Lab
//
// SPDX-License-Identifier: Apache-2.0

use core::fmt;
use sentry_uapi::{syscall, copy_to_kernel};

struct LogSink;

/// Write trait impl for LogSink type
impl fmt::Write for LogSink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let raw = s.as_bytes();
        let _ = copy_to_kernel(&raw);
        syscall::log(raw.len());
        Ok(())
    }
}

/// public print entrypoint called by macro rules
pub fn _print(args: fmt::Arguments) {
    use core::fmt::Write;
    LogSink.write_fmt(args).expect("Print failed");
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        ($crate::print::_print(format_args!($($arg)*)))
    }
}

/// println macro implementation for shield/sentry based application
#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)))
}
