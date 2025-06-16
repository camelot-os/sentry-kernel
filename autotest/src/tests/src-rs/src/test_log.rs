// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

use core::fmt;
use sentry_uapi::syscall::log;

pub const USER_AUTOTEST: &str = "[AT]";
pub const USER_AUTOTEST_INFO: &str = "[INFO      ]";
pub const USER_AUTOTEST_EXEC: &str = "[EXE       ]";
pub const USER_AUTOTEST_START: &str = "[START     ]";
pub const USER_AUTOTEST_END: &str = "[END       ]";
pub const USER_AUTOTEST_FAIL: &str = "[KO        ]";
pub const USER_AUTOTEST_SUCCESS: &str = "[SUCCESS   ]";
pub const USER_AUTOTEST_START_SUITE: &str = "[STARTSUITE]";
pub const USER_AUTOTEST_END_SUITE: &str = "[ENDSUITE  ]";
const SVC_EXCH_AREA_LEN: usize = 128;
struct DebugPrint;

impl fmt::Write for DebugPrint {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let max_length = s.len().min(SVC_EXCH_AREA_LEN);
        unsafe { copy_from_user(s.as_ptr(), max_length) };
        log(max_length);
        Ok(())
    }
}

pub fn _print(args: fmt::Arguments) {
    use core::fmt::Write;
    DebugPrint.write_fmt(args).expect("Print failed");
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        $crate::test_log::_print(format_args!($($arg)*))
    }
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)))
}

// Macros

#[macro_export]
macro_rules! test_start {
    () => {
        $crate::println!("[START     ] {}:{}", core::module_path!(), core::line!());
    };
}

#[macro_export]
macro_rules! test_end {
    () => {
        $crate::println!("[END       ] {}:{}", core::module_path!(), core::line!());
    };
}

#[macro_export]
macro_rules! test_suite_start {
    ($msg:expr) => {
        $crate::println!(
            "[STARTSUITE] {}: {} @{}",
            core::module_path!(),
            $msg,
            core::line!()
        );
    };
}

#[macro_export]
macro_rules! test_suite_end {
    ($msg:expr) => {
        $crate::println!(
            "[ENDSUITE  ] {}: {} @{}",
            core::module_path!(),
            $msg,
            core::line!()
        );
    };
}

#[macro_export]
macro_rules! log_line {
    ($prefix:expr, $fmt:expr $(, $arg:expr)* $(,)?) => {
        $crate::println!("{} {}:{}: {}", $prefix, core::module_path!(), core::line!(), core::format_args!($fmt $(, $arg)*));
    };
}

#[macro_export]
macro_rules! check_eq {
    ($a:expr, $b:expr) => {{
        if $a == $b {
            log_line!("[SUCCESS   ]", "{:?} == {:?}", $a, $b);
            true
        } else {
            log_line!("[KO        ]", "{:?} != {:?}", $a, $b);
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
