
# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

frama_c = find_program('frama-c', required: true, native: true)
z3 = find_program('z3', required: true, native: true)
cvc4 = find_program('cvc4', 'cvc4-1.7', required: true, native: true)


# Part 1: analysis from kernel entrypoint. These targets check the call graph from
# the kernel entrypoint itelf, analysing the overall init sequence of the kernel.
# Here, all the probing, platform initialization, etc. is executed through the
# real kernel entrypoint

# overall kernel generated headers and/or sources must be made before testing
# Although, they are not passed to framaC directly, which get back sources but not
# headers themselves
framac_dep = custom_target(
    command: [ 'true' ],
    input: [
      arch_header_set_config.sources(),
      arch_source_set_config.sources(),
      bsp_header_set_config.sources(),
      bsp_private_gen_header_set_config.sources(),
      bsp_private_gen_source_set_config.sources(),
      bsp_private_header_set_config.sources(),
      bsp_source_set_config.sources(),
      managers_header_set_config.sources(),
      managers_private_gen_header_set_config.sources(),
      managers_private_gen_source_set_config.sources(),
      managers_private_header_set_config.sources(),
      managers_source_set_config.sources(),
      sched_header_set_config.sources(),
      sched_source_set_config.sources(),
      sentry_header_set_config.sources(),
      syscall_header_set_config.sources(),
      syscall_source_set_config.sources(),
      zlib_header_set_config.sources(),
      zlib_source_set_config.sources(),
    ],
    output: 'framac.dep',
)

framac_dep_tree = meson.current_build_dir() / 'framac.dep.p'

# To avoid duplication between formal proof tests, a dedicated lib is written
# to hold various Frama-C related high level tooling
subdir('libproof')

# Only kernel C sources here (not headers)
kernel_sources = [
    sentry_startup,
    bsp_source_set_config.sources(),
    arch_source_set_config.sources(),
    sched_source_set_config.sources(),
    managers_source_set_config.sources(),
    syscall_source_set_config.sources(),
    zlib_source_set_config.sources(),
]

# NOTE: in proof mode, if not generated in kernel library corresponding dep dir,
# all generator's headers have been generated in framac.dep.d dir (see framac_dep definition above)
framac_gen_opts = [
  '-kernel-msg-key', 'pp',
  '-kernel-warn-key', 'c11=inactive,parser:unsupported=feedback',
  '-kernel-debug','1',
  '-machdep', 'gcc_x86_32',
  '-instantiate',
  '-json-compilation-database', join_paths(meson.project_build_root(), 'compile_commands.json'),
  '-config', join_paths(meson.current_build_dir(), '.sentry-config'),
  '-cpp-extra-args=-nostdinc,-I ' + framac_dep_tree + ',-DDTS_FILE=\\"@0@\\"'.format(sentry_dts_file),
  '-frama-c-stdlib',
  '-absolute-valid-range', '40000000-0xE000F000',

]

framac_rte_eva_opts = [
 '-rte',
 '-warn-left-shift-negative',
 '-warn-right-shift-negative',
 '-warn-signed-downcast',
 '-warn-signed-overflow',
 '-warn-unsigned-downcast',
 '-warn-unsigned-overflow',
 '-warn-invalid-pointer',
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
]

framac_wp_opts = [
  '-wp',
  '-wp-dynamic',
  '-wp-model', 'Typed+ref+int',
  '-wp-literals',
  '-wp-timeout', '15',
  '-wp-smoke-tests',
  '-wp-prover','alt-ergo,cvc4,z3,tip',
  '-wp-time-margin', '25',
  '-wp-no-smoke-dead-code',
  '-wp-no-smoke-dead-call',
]

framac_md_opts = [
  '-mdr-gen', 'md',
  '-mdr-title', 'Sentry kernel noRTE report',
]

#'-wp-prop="-@lemma"',



kernel_entrypoint = files(
  join_paths(meson.project_source_root(), 'kernel/src/startup/entrypoint.c'),

)


test(
  'frama-C-parsing',
  frama_c,
  args: [
    kernel_entrypoint, kernel_sources,
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'frama-c-parsing-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'frama-c-parsing-sentry-all.log'),
    '-main', '_entrypoint',
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), 'frama-c-parsing')},
  suite: 'proof',
  depends: [ framac_dep ],
  timeout: 120,
  is_parallel: false,
  priority: 255,
)



# check the number of red alarms emitted by eva
# the first line always describes result's columns type
# a noRTE program should hold only that line
# NOTE: ARM CMSIS headers uninitialized alarms are not considered as they
# are the consequence of uninitialized consideration, while HW is reset-time initialized
redalarmcount_py_wrapper = '''
import sys
import re

lines=0
with open(sys.argv[1], 'r') as fp:
  for line in fp:
       if not re.search('include/cmsis\s.*\sinitialization\s', line):
          lines += 1
       else:
           print(line)
  print('found ' + str(lines-1) + ' alarms')
exit(0)
'''

subdir('proof_entrypoint')
subdir('proof_handlers')
subdir('proof_composition')
