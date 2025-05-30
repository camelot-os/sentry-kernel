# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

kernel_eva_zlib_string_entypoint = files(
  'kernel_zlib_string.c',
)

kernel_eva_zlib_crypto_entypoint = files(
  'kernel_zlib_crypto.c',
)

framac_stub_zlib_elf = executable(
    test_name,
    name_suffix: 'elf',
    sources: [ kernel_eva_zlib_string_entypoint, kernel_eva_zlib_crypto_entypoint ],
    include_directories: kernel_inc,
    dependencies: [ sentry_zlib_dep, external_deps, proof_lib_dep ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

test_name = 'frama-c-zlib-string-wp'

# zlib exported functions to be proved
zlib_string_correctness_targets = ','.join(
  [
    # string.h local unreachable utilities subprograms
    '__sentry_strnlen',
    '__sentry_memset',
    '__sentry_memcpy',
    '__regions_overlaps',
    # string.h exported (through aliasing) functions
    'sentry_strnlen',
    'sentry_memset',
    'sentry_memcpy',
    # Frama-C specific functions and entrypoint for EVA
    'kernel_zlib',
    'test_memset',
  ])


test(
  test_name,
  frama_c,
  args: [
    kernel_eva_zlib_string_entypoint, zlib_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'kernel_zlib',
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
    '-wp-fct', zlib_string_correctness_targets,
    '-wp-log', 'a:'+ join_paths(meson.current_build_dir(), test_name + '-proofs.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), test_name)},
  suite: 'proof',
  timeout: 1200,
  is_parallel: false,
  priority: 254,
)

# testing crypto part of zlib (pcg32+crc32)
test_name = 'frama-c-zlib-crypto-wp'

# zlib exported functions to be proved
zlib_crypto_correctness_targets = ','.join(
  [
    # PGC32 functions
    'pcg32_seed',
    'pcg32',
  ])

test(
  test_name,
  frama_c,
  args: [
    kernel_eva_zlib_crypto_entypoint, zlib_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), test_name + '-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), test_name + '-all.log'),
    '-main', 'kernel_zlib',
    '-rte',
    '-no-warn-signed-downcast',
    '-no-warn-unsigned-downcast',
    '-eva',
    '-eva-builtins-auto',
    '-eva-show-perf',
    '-eva-slevel', '500',
    '-eva-split-limit', '256',
    '-eva-domains', 'symbolic-locations',
    '-eva-domains', 'equality',
    '-eva-split-return', 'auto',
    '-eva-partition-history', '1',
    '-remove-redundant-alarms',
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
    '-wp-fct', zlib_crypto_correctness_targets,
    '-wp-log', 'a:'+ join_paths(meson.current_build_dir(), test_name + '-proofs.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), test_name)},
  suite: 'proof',
  timeout: 1200,
  is_parallel: false,
  priority: 254,
)
