# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
# this allows custom entrypoint for, typically, syscall entrypoints coverage
frama_c_eva_norte_svc_entrypoint = files(
  'handler.c',
)

test_name = 'frama-c-eva-handler-svc'

framac_stub_elf = executable(
    test_name + '-entrypoint',
    name_suffix: 'elf',
    sources: [ frama_c_eva_norte_svc_entrypoint, framac_dep ],
    include_directories: kernel_inc,
    dependencies: [ external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

# testing EVA/noRTE through kernel svc handler
test(
 test_name,
 frama_c,
 args: [
    frama_c_eva_norte_svc_entrypoint, kernel_sources,
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'handler_entrypoint',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), test_name + '.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), test_name + '.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-by-function',
    '-metrics-output',join_paths(meson.current_build_dir(), test_name + '.json'),
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

# FIXME: the svc exchange manipulation is not yet proven, generating an exit 1 (1 RTE) as
# this part is not demonstrated and accepted by frama-C by now
test(
  test_name + '-redalarm',
  py3,
  args: [
    '-c',
    redalarmcount_py_wrapper,
    join_paths(meson.current_build_dir(), test_name + '.red'),
  ],
  depends: [ framac_dep ],
  suite: 'proof',
  is_parallel: false,
  priority: 253,
)
