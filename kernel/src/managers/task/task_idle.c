// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <string.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include "task_init.h"
#include "task_idle.h"

/**
 * ldscript provided
 */
extern size_t _idle_svcexchange;
extern size_t _sidle;
extern size_t _eidle;

static task_meta_t idle_meta;

void task_idle_init(void)
{
    memset((void*)&idle_meta, 0x0, sizeof(task_meta_t));

    idle_meta.label = SCHED_IDLE_TASK_LABEL;
    idle_meta.magic = CONFIG_TASK_MAGIC;
    idle_meta.flags.start_mode = JOB_FLAG_START_NOAUTO;
    idle_meta.flags.exit_mode = JOB_FLAG_EXIT_PANIC;
    idle_meta.s_text = (size_t)&_sidle;
    idle_meta.text_size = ((size_t)&_eidle - (size_t)&_sidle);

#if defined(__arm__) || defined(__FRAMAC__)
    idle_meta.entrypoint_offset = 0x1UL;
#elif defined(CONFIG_ARCH_RV32)
    idle_meta.entrypoint_offset = 0x0UL;
#else
#error "unsupported architecture!"
#endif
    idle_meta.finalize_offset = 0x0UL; /* TBD for idle */
    idle_meta.rodata_size = 0UL;
    idle_meta.got_size = 0UL;
    idle_meta.data_size = 4UL; /* ssp seed value initial data size */
    idle_meta.bss_size = 0UL;
    idle_meta.heap_size = 0UL;
    idle_meta.s_svcexchange = (size_t)&_idle_svcexchange;
    idle_meta.stack_size = 256; /* should be highly enough */
}

task_meta_t *task_idle_get_meta(void)
{
    return &idle_meta;
}
