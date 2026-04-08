# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

kernel_eva_entypoint = files(
  'kernel_entrypoint.c',
)

test_name = 'frama-c-eva-entrypoint'

framac_stub_entrypoint_elf = executable(
    test_name + '-entrypoint',
    name_suffix: 'elf',
    sources: [ kernel_eva_entypoint, kernel_entrypoint, framac_dep ],
    include_directories: kernel_inc,
    dependencies: [ external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

# testing EVA/noRTE through kernel bootup entrypoint (init phase)
# we define SCB memory as accessible
test(
  test_name,
 frama_c,
 args: [
    kernel_entrypoint,
    kernel_eva_entypoint,
    kernel_sources,
    framac_gen_opts,
    '-absolute-valid-range', '0x40000000-0xE000F000',
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'kernel_entrypoint',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), test_name + '.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), test_name + '.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-by-function',
    '-metrics-output',join_paths(meson.current_build_dir(), test_name + '-coverage.json'),
    '-save',join_paths(meson.current_build_dir(), test_name + '.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), test_name + '-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '-md.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), test_name)},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 600,
  is_parallel: false,
  priority: 254,
)

test(
  test_name + '-redalarm',
  py3,
  args: [
    '-c',
    redalarmcount_py_wrapper,
    join_paths(meson.current_build_dir(), test_name + '.red'),
  ],
  depends: [ framac_dep ],
  suite: 'proof-postanalysis',
  is_parallel: false,
  priority: 1,
)
