// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include <uapi/uapi.h>
#include "test_log.h"
#include "test_respawn.h"

void test_respawn_bootcheck(void)
{
    if (__sys_has_respawned() == STATUS_AGAIN) {
        /* first instance, nothing to be done */
        goto end;
    } else {
        /* if the task has been respawned */
        TEST_START();
        LOG("task has been respawned successfully");
        /* exiting with invalid return code to terminate without respawning */
        TEST_END();
        printf("AUTOTEST END\n");
        /* to avoid any further execution through respawn, we loop on yield() here */
        while (1) {
            __sys_sched_yield();
        }
    }
end:
    return;
}

void test_respawn(void)
{
    __sys_exit(0);
}
