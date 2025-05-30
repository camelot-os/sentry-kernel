# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
framac_bsp_rcc_stub_entrypoint = files(
  'main.c',
)

framac_bsp_rcc_stub_elf = executable(
    'framac_bsp_rcc_stub_exe',
    name_suffix: 'elf',
    sources: [
      framac_bsp_rcc_stub_entrypoint,
      framac_dep,
    ],
    include_directories: kernel_inc,
    dependencies: [ external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    build_by_default: false,
)

frama_c_rcc_source_set = ssmod.source_set()
frama_c_rcc_source_set.add(
  framac_bsp_rcc_stub_entrypoint,
)
# include Clock subcomponent private source set
frama_c_rcc_source_set.add_all(bsp_clk_source_set, bsp_clk_private_gen_source_set)

# forge the global resulting sources list
frama_c_rcc_source_set_config = frama_c_rcc_source_set.apply(kconfig_data, strict: false)

test_name = 'frama-c-wp-bsp-rcc'

test(
  test_name,
  frama_c,
  args: [
    frama_c_rcc_source_set_config.sources(),
    framac_gen_opts,
    '-absolute-valid-range', '0x40000000-0xE000F000',
    framac_rte_eva_opts,
    '-eva-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '.log'),
    '-eva-report-red-statuses', join_paths(meson.current_build_dir(), test_name + '-statuses.log'),
    '-metrics',
    '-metrics-eva-cover',frama_c_rcc_source_set_config.sources(),
    '-then',
    framac_wp_opts,
    '-wp-fct','rcc_probe,rcc_get_core_frequency,rcc_enable,rcc_disable,rcc_get_bus_clock,rcc_mux_select_clock_source',
    '-wp-log', 'a:'+join_paths(meson.current_build_dir(), test_name + '-wp.log'),
    '-save',join_paths(meson.current_build_dir(), test_name + '.wp'),
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
