# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

test_name = 'frama-c-wp-bsp-exti'
# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
framac_bsp_exti_stub_entrypoint = files(
  'main.c',
)

framac_bsp_exti_stub_elf = executable(
    'framac_bsp_exti_stub_exe',
    name_suffix: 'elf',
    sources: [
      framac_bsp_exti_stub_entrypoint,
      framac_dep,
    ],
    include_directories: kernel_inc,
    dependencies: [ external_deps],
    c_args: [ target_arch_args, global_build_args, proof_lib_dep ],
    install: false,
    build_by_default: false,
)

framac_exti_sources = [
  meson.current_source_dir() / 'main.c',
  meson.project_source_root() /'kernel/src/drivers/exti/stm32-exti.c',
]

test(
  test_name,
  frama_c,
  args: [
    framac_exti_sources,
    framac_gen_opts,
    '-absolute-valid-range', '0x40000000-0xE000F000',
    framac_rte_eva_opts,
    '-eva-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '.log'),
    '-eva-report-red-statuses', join_paths(meson.current_build_dir(), test_name + '-red-statuses.log'),
    '-metrics',
    '-metrics-eva-cover',meson.project_source_root()+'/kernel/src/drivers/exti/stm32-exti.c',
    '-metrics-by-function',
    '-then', framac_wp_opts,
    '-wp-fct', 'exti_probe,exti_mask_interrupt,exti_unmask_interrupt,exti_mask_event,exti_unmask_event,exti_generate_swinterrupt,exti_clear_pending',
    '-wp-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '-wp.log'),
    '-save',join_paths(meson.current_build_dir(), test_name + '.wp.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), test_name + '-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '-md.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), '.frama-c')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 1200,
)
