// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

pub const USER_AUTOTEST: &str = "[AT]";
pub const USER_AUTOTEST_INFO: &str = "[INFO      ]";
pub const USER_AUTOTEST_EXEC: &str = "[EXE       ]";
pub const USER_AUTOTEST_START: &str = "[START     ]";
pub const USER_AUTOTEST_END: &str = "[END       ]";
pub const USER_AUTOTEST_FAIL: &str = "[KO        ]";
pub const USER_AUTOTEST_SUCCESS: &str = "[SUCCESS   ]";
pub const USER_AUTOTEST_START_SUITE: &str = "[STARTSUITE]";
pub const USER_AUTOTEST_END_SUITE: &str = "[ENDSUITE  ]";

#[macro_export]
macro_rules! test_start {
    () => {
        $crate::println!("[AT][START     ] {}:{}", core::module_path!(), core::line!());
    };
}

#[macro_export]
macro_rules! test_end {
    () => {
        $crate::println!("[AT][END       ] {}:{}", core::module_path!(), core::line!());
    };
}

#[macro_export]
macro_rules! test_suite_start {
    ($msg:expr) => {
        $crate::println!(
            "[AT][STARTSUITE] {}: {} @{}",
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
            "[AT][ENDSUITE  ] {}: {} @{}",
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
            log_line!("[AT][SUCCESS   ]", "{:?} == {:?}", $a, $b);
            true
        } else {
            log_line!("[AT][KO        ]", "{:?} != {:?}", $a, $b);
            false
        }
    }};
}

#[macro_export]
macro_rules! check {
    ($cond:expr, $msg:literal $(, $arg:expr)* $(,)?) => {{
        if $cond {
            log_line!("[AT][SUCCESS   ]", $msg $(, $arg)*);
            true
        } else {
            log_line!("[AT][KO        ]", $msg $(, $arg)*);
            false
        }
    }};
}
