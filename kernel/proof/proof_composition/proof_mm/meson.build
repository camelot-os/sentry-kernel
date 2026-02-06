# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

kernel_eva_mm_map_entypoint = files(
  'kernel_map_resource.c',
)


framac_stub_mm_elf = executable(
    test_name,
    name_suffix: 'elf',
    sources: [ kernel_eva_mm_map_entypoint, framac_dep ],
    include_directories: kernel_inc,
    dependencies: [ external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

test_name = 'frama-c-mm-map-wp'

# MPU memory-map related functions to be proved
mm_map_correctness_targets = ','.join(
  [
    'task_get_from_handle',
    'mgr_task_get_num',
    'ktaskh_to_taskh',
    'mgr_task_add_resource',
    'mpu_regions_overlap',
    'mpu_region_is_valid',
    'mpu_forge_resource',
    'mpu_forge_unmapped_ressource',
    'mpu_convert_size_to_region',
    'mgr_mm_forge_empty_table',
    'mgr_mm_forge_ressource',
    '__mpu_fastload',
    '__mpu_is_resource_free',
    '__mpu_get_resource_base_address',
    '__mpu_region_align_size',
    '__mpu_size_to_region',
  ])


test(
  test_name,
  frama_c,
  args: [
    kernel_eva_mm_map_entypoint,
    arch_source_set_config.sources(),
    managers_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'map_resource',
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
    framac_wp_opts,
    '-wp-fct', mm_map_correctness_targets,
    '-wp-log', 'a:'+ join_paths(meson.current_build_dir(), test_name + '-proofs.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), test_name)},
  suite: 'proof',
  timeout: 3600,
  is_parallel: false,
  priority: 254,
)
