// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

macro_rules! syscall0 {
    ($id:expr) =>{{
        let res: u32;
        unsafe {
            asm!(
                "svc #{}",
                const ($id as u8),
                lateout("r0") res,
                options(preserves_flags)
            );
        }
        res
    }}
}

macro_rules! syscall1 {
    ($id:expr, $arg0:expr) => {{
        let res: u32;
        unsafe { asm!(
                "svc #{}",
                const ($id as u8),
                inlateout("r0") $arg0 => res,
                options(preserves_flags)
            ); }
        res
    }}
}

macro_rules! syscall2 {
    ($id:expr, $arg0:expr, $arg1:expr) => {{
        let res: u32;
        unsafe { asm!(
                "svc #{}",
                const ($id as u8),
                inlateout("r0") $arg0 => res,
                in("r1") $arg1,
                options(preserves_flags)
            ); }
        res
    }}
}

macro_rules! syscall3 {
    ($id:expr, $arg0:expr, $arg1:expr, $arg2:expr) => {{
        let res: u32;
        unsafe { asm!(
                "svc #{}",
                const ($id as u8),
                inlateout("r0") $arg0 => res,
                in("r1") $arg1,
                in("r2") $arg2,
                options(preserves_flags)
            ); }
        res
    }}
}

macro_rules! syscall {
    ($id:expr) => {
        syscall0!($id)
    };
    ($id:expr, $arg0:expr) => {
        syscall1!($id, $arg0)
    };
    ($id:expr, $arg0:expr, $arg1:expr) => {
        syscall2!($id, $arg0, $arg1)
    };
    ($id:expr, $arg0:expr, $arg1:expr, $arg2:expr) => {
        syscall3!($id, $arg0, $arg1, $arg2)
    };
}
