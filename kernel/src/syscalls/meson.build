# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

syscall_source_set = ssmod.source_set()

syscalls = files(
    'sysgate_send_ipc.c',
    'sysgate_send_signal.c',
    'sysgate_waitforevent.c',
    'sysgate_gpio.c',
    'sysgate_get_devhandle.c',
    'sysgate_int_acknowledge.c',
    'sysgate_int_enable.c',
    'sysgate_int_disable.c',
    'sysgate_map.c',
    'sysgate_exit.c',
    'sysgate_get_prochandle.c',
    'sysgate_yield.c',
    'sysgate_sleep.c',
    'sysgate_start.c',
    'sysgate_get_random.c',
    'sysgate_pm_manage.c',
    'sysgate_pm_setclock.c',
    'sysgate_alarm.c',
    'sysgate_get_cycle.c',
    'sysgate_log.c',
    'sysgate_get_shmhandle.c',
    'sysgate_get_dmahandle.c',
    'sysgate_shm_set_creds.c',
    'sysgate_shm_get_infos.c',
    'sysgate_dma_get_info.c',
    'sysgate_dma_assign.c',
    'sysgate_dma_unassign.c',
    'sysgate_dma_start.c',
    'sysgate_dma_suspend.c',
    'sysgate_dma_resume.c',
)

syscall_source_set.add(syscalls)

if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
    syscall_source_set.add(files('sysgate_autotest.c'))
endif

syscall_source_set_config = syscall_source_set.apply(kconfig_data, strict:false)

sentry_syscall_lib = static_library('sentry_syscall',
    sources: [
        syscall_source_set_config.sources(),
        syscall_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    c_args: [ target_arch_args, global_build_args, activated_lib_hardening_cflags ],
    install: false,
    dependencies: [
        sentry_arch_dep,
        sentry_managers_dep,
        sentry_zlib_dep,
        syscall_source_set_config.dependencies(),
        external_deps
    ],
)

sentry_syscall_dep = declare_dependency(
    link_with: sentry_syscall_lib,
    sources: syscall_header_set_config.sources(),
    include_directories: kernel_inc,
)
