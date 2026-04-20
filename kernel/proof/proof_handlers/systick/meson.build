# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
# this allows custom entrypoint for, typically, syscall entrypoints coverage
frama_c_norte_systick_entrypoint = files(
  'handler_systick.c',
)

framac_stub_elf = executable(
    'framac_norte_systick_entrypoint',
    name_suffix: 'elf',
    sources: [frama_c_norte_systick_entrypoint, framac_dep ],
    include_directories: kernel_inc,
    dependencies: [ external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

# testing EVA/noRTE through kernel svc handler
test(
  'frama-C-eva-handler-systick',
 frama_c,
 args: [
    frama_c_norte_systick_entrypoint, kernel_sources,
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick-all.log'),
    '-main', 'handler_entrypoint',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-by-function',
    '-metrics-output',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick-coverage.json'),
    '-save',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick-md.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 600,
  is_parallel: false,
  priority: 254,
)

test(
  'frama-C-eva-handler-systick-redalarm',
  py3,
  args: [
    '-c',
    redalarmcount_py_wrapper,
    join_paths(meson.current_build_dir(), 'frama-c-eva-handler-systick.red'),
  ],
  depends: [ framac_dep ],
  suite: 'proof',
  is_parallel: false,
  priority: 253,
)
