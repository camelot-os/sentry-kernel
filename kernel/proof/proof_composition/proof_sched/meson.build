# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

test_name = 'frama-c-sched-eva'

kernel_eva_sched_entypoint = files(
  'kernel_sched.c',
)

framac_stub_sched_elf = executable(
    test_name,
    name_suffix: 'elf',
    sources: [ kernel_eva_sched_entypoint, sentry_header_set_config.sources(), sched_source_set_config.sources() ],
    include_directories: kernel_inc,
    dependencies: [ external_deps, sentry_sched_dep, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)


test(
  test_name,
  frama_c,
  args: [
    kernel_eva_sched_entypoint,
    sched_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'kernel_sched',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), test_name + '.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), test_name + '.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-output',join_paths(meson.current_build_dir(), test_name + '-coverage.json'),
    '-save',join_paths(meson.current_build_dir(), test_name + '.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), test_name + '-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '-md.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), test_name)},
  suite: 'proof',
  timeout: 1200,
  is_parallel: false,
  priority: 254,
)
