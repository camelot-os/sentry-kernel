# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

sched_source_set = ssmod.source_set()

# schedulers implementations
sentry_sched_fifo_c = files(
    'sched_fifo.c',
)
sentry_sched_rrmq_c = files(
    'sched_rrmq.c',
)
sentry_sched_rma_c = files(
    'sched_rma.c',
)

sched_source_set.add(when: 'CONFIG_SCHED_FIFO', if_true: sentry_sched_fifo_c)
sched_source_set.add(when: 'CONFIG_SCHED_RRMQ', if_true: sentry_sched_rrmq_c)
sched_source_set.add(when: 'CONFIG_SCHED_RMA', if_true: sentry_sched_rma_c)

sched_source_set_config = sched_source_set.apply(kconfig_data, strict: false)

sentry_sched_lib = static_library('sentry_sched',
    sources: [
        sched_source_set_config.sources(),
        sched_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    c_args: [ target_arch_args, global_build_args, activated_lib_hardening_cflags ],
    install: false,
    dependencies: [
        sentry_arch_dep,
        sentry_managers_dep,
        sched_source_set_config.dependencies(),
        external_deps
    ],
)

sentry_sched_dep = declare_dependency(
    link_with: sentry_sched_lib,
    sources: sched_header_set_config.sources(),
    include_directories: kernel_inc,
)
