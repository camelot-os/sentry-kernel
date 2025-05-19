// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#![no_std]

use core::ffi::c_char;
use core::fmt::{self, Write};

extern "C" {
    fn printf(fmt: *const c_char, ...) -> i32;
}

const USER_AUTOTEST: &str = "[AT]";
const USER_AUTOTEST_INFO: &str = "[INFO      ]";
const USER_AUTOTEST_EXEC: &str = "[EXE       ]";
const USER_AUTOTEST_START: &str = "[START     ]";
const USER_AUTOTEST_END: &str = "[END       ]";
const USER_AUTOTEST_FAIL: &str = "[KO        ]";
const USER_AUTOTEST_SUCCESS: &str = "[SUCCESS   ]";
const USER_AUTOTEST_START_SUITE: &str = "[STARTSUITE]";
const USER_AUTOTEST_END_SUITE: &str = "[ENDSUITE  ]";

// Rust Wrapper for printf,  UTF-8 / ASCII C-string ended by null
fn c_log(prefix: &str, file: &str, line: u32, msg: &str) {
    let _ = unsafe {
        printf(
            b"%s%s %s:%d: %s\n\0".as_ptr().cast(),
            USER_AUTOTEST.as_ptr(),
            prefix.as_ptr(),
            file.as_ptr(),
            line,
            msg.as_ptr(),
        )
    };
}

// Convert &str statics into *const c_char
trait AsCStr {
    fn as_ptr(&self) -> *const c_char;
}

impl AsCStr for &str {
    fn as_ptr(&self) -> *const c_char {
        (*self).as_bytes().as_ptr().cast()
    }
}

// Macros

#[macro_export]
macro_rules! test_start {
    () => {
        $crate::test_log::c_log(
            $crate::test_log::USER_AUTOTEST_START,
            core::module_path!(),
            core::line!(),
            "",
        )
    };
}

#[macro_export]
macro_rules! test_end {
    () => {
        $crate::test_log::c_log(
            $crate::test_log::USER_AUTOTEST_END,
            core::module_path!(),
            core::line!(),
            "",
        )
    };
}

#[macro_export]
macro_rules! test_suite_start {
    ($msg:expr) => {
        $crate::test_log::c_log(
            $crate::test_log::USER_AUTOTEST_START_SUITE,
            core::module_path!(),
            core::line!(),
            $msg,
        )
    };
}

#[macro_export]
macro_rules! test_suite_end {
    ($msg:expr) => {
        $crate::test_log::c_log(
            $crate::test_log::USER_AUTOTEST_END_SUITE,
            core::module_path!(),
            core::line!(),
            $msg,
        )
    };
}

#[macro_export]
macro_rules! log_info {
    ($fmt:expr $(, $arg:expr)* $(,)?) => {
        let s = format_args!($fmt $(, $arg)*);
        use core::fmt::Write;
        let mut buf = [0u8; 256];
        let _ = write!(&mut $crate::test_log::FmtBuf::new(&mut buf), "{}", s);
        $crate::test_log::c_log(
            $crate::test_log::USER_AUTOTEST_INFO,
            core::module_path!(),
            core::line!(),
            core::str::from_utf8(&buf).unwrap_or(""),
        );
    };
}


pub struct FmtBuf<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> FmtBuf<'a> {
    pub fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, pos: 0 }
    }
}

impl<'a> Write for FmtBuf<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let len = core::cmp::min(s.len(), self.buf.len().saturating_sub(self.pos));
        self.buf[self.pos..self.pos + len].copy_from_slice(&s.as_bytes()[..len]);
        self.pos += len;
        Ok(())
    }
}

#[macro_export]
macro_rules! check_eq {
    ($a:expr, $b:expr) => {{
        if $a == $b {
            log_line!("[SUCCESS   ]", "{} == {}", $a, $b);
            true
        } else {
            log_line!("[KO        ]", "{} != {}", $a, $b);
            false
        }
    }};
}

#[macro_export]
macro_rules! check {
    ($cond:expr, $msg:literal $(, $arg:expr)* $(,)?) => {{
        if $cond {
            log_line!("[SUCCESS   ]", $msg $(, $arg)*);
            true
        } else {
            log_line!("[KO        ]", $msg $(, $arg)*);
            false
        }
    }};
}
