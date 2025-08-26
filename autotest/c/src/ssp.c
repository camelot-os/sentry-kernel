// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi/uapi.h>

void __stack_chk_fail(void)
{
    /* End of task. NOTE: stack corruption is a serious security issue */
    __sys_exit(STATUS_CRITICAL);
    while (1) {
    };
}
