# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
framac_wp_arch_stub_entrypoint = files(
  'main_arch.c',
)

framac_stub_arch_elf = executable(
    test_name,
    name_suffix: 'elf',
    sources: [ framac_wp_arch_stub_entrypoint ],
    include_directories: kernel_inc,
    dependencies: [ sentry_arch_dep, external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)


test_name = 'frama-c-wp-arch'


test(
  'frama-C-wp-arch',
  frama_c,
  args: [
    framac_wp_arch_stub_entrypoint, arch_source_set_config.sources(),
    framac_gen_opts,
    '-absolute-valid-range', '0x20000000-0xE000F000',
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'kernel_arch',
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
    '-then', framac_wp_opts,
    '-wp-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '-wp.log'),
    '-save',join_paths(meson.current_build_dir(), test_name + '.wp'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), '.frama-c')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 7200,
)
