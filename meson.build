# SPDX-License-Identifier: Apache-2.0
#
# Copyright 2023-2024 Ledger SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

project('sentry-kernel', 'c',
        version: '>=1.4.0',
    default_options: [
        'c_std=gnu11', 'cpp_std=gnu++20',
        'warning_level=3', 'optimization=s',
        'default_library=static', 'b_pie=false', 'b_staticpic=false',
        'licensedir=share/info/sentry-kernel',
        'pkgconfig.relocatable=true',
    ],
    version : run_command('support/meson/version.sh', 'get-vcs', check: true).stdout().strip(),
    license: 'Apache-2.0',
    license_files: [ 'LICENSE' ],
)

meson.add_dist_script('support/meson/version.sh', 'set-dist', meson.project_version())

compiler = meson.get_compiler('c', native: false)

objcopy = find_program('objcopy')
sentry_install_script = find_program('support/scripts/install.py')

keyval = import('keyval')
fs = import('fs')
pymod = import('python')
ssmod = import('sourceset')

py3 = pymod.find_installation('python3')

kconfig_file = meson.current_source_dir() / 'Kconfig'
kconfig_proj = subproject('kconfig', default_options: ['kconfig=@0@'.format(kconfig_file)])
kconfig_h = kconfig_proj.get_variable('kconfig_h')
kconfig_rustargs = kconfig_proj.get_variable('kconfig_rustargs')
kconfig_data = kconfig_proj.get_variable('kconfig_data')

# Testing high security flags of cross compiler. These are gcc 13-14 hardening flags.
# See https://gcc.gnu.org/onlinedocs/gcc-14.1.0/gcc/Instrumentation-Options.html#index-fharden-compares
# for more information about each flag
activated_hardening_cflags = []
hardening_cflags = [
    '-fstack-clash-protection',
]

if kconfig_data.get('CONFIG_SECU_ENFORCE_COMPARE', 0) == 1
hardening_cflags += [
  '-fharden-compares',
  '-fharden-conditional-branches',
]
endif


foreach cflag: hardening_cflags
  if compiler.has_argument(cflag)
    activated_hardening_cflags += cflag
  endif
endforeach

# some hardening flags are not compatible with nacked function, making compilation fails
# this flags are not included at global level but at lib level instead
activated_lib_hardening_cflags = []
lib_hardening_cflags = []

if kconfig_data.get('CONFIG_SECU_ENFORCE_CFI', 0) == 1
lib_hardening_cflags += [
  '-fharden-control-flow-redundancy',
]
endif

if kconfig_data.get('CONFIG_SECU_ENFORCE_RETURNING_CALLS', 0) == 1
lib_hardening_cflags += [
  '-fhardcfr-check-returning-calls',
]
endif


foreach cflag: lib_hardening_cflags
  if compiler.has_argument(cflag)
    activated_lib_hardening_cflags += cflag
  endif
endforeach


external_deps = []

global_build_args = [
    '-include', fs.parent(kconfig_h) / fs.name(kconfig_h),
    '-ffreestanding',
    '-fno-builtin',
    '-nostdlib',
    '-fno-common',
    '-fdata-sections',
    '-ffunction-sections',
    '-Wno-pedantic', # FIXME: to analyze bits.h (not pedantic compatible)
    '-Wno-unused-function', # FIXME: while in early dev
    '-Wno-unused-variable', # FIXME: while in early dev
    '-Wno-unused-parameter', # FIXME: while in early dev
    activated_hardening_cflags,
]

# Deprecated kconfig entry handling, to be removed on next major release
if kconfig_data.has('CONFIG_TASK_MAGIC_VALUE')
    warning('Deprecated kconfig entry CONFIG_TASK_MAGIC_VALUE, please update config file')
    global_build_args += [
        '-DCONFIG_TASK_MAGIC=@0@'.format(kconfig_data.get('CONFIG_TASK_MAGIC_VALUE'))
    ]
endif

# these flags are overload by arch/<architecture> meson.build file
target_arch_args = []

target_link_args = [
    '-Wl,--gc-sections',
    '-Wl,--no-undefined',
    '-Wl,--cref',
    '-nostdlib',
    '-nodefaultlibs',
    '-nostartfiles',
]

add_project_link_arguments(target_link_args, language: 'c', native: false)

# XXX: add_global_arguments **can't** be done after a subproject definition
#add_global_arguments([ global_build_args, target_arch_args ], language: 'c', native: false)
global_host_c_args_str = ','.join(global_build_args)

# for ARM targets, using CMSIS headers
if kconfig_data.get('CONFIG_ARCH_ARM', 0) == 1
cmsis_proj = subproject('cmsis', default_options: ['c_args=@0@'.format(global_host_c_args_str)])
cmsis_dep = cmsis_proj.get_variable('cmsis_dep')
external_deps += cmsis_dep
endif

# meson svd subproject and associated variables
# XXX: Using a default option here may lead to weird results if one changes the kconfig
# may be use a generator and process in the top level project ?!?
kadoc_proj = subproject('kadoc',  default_options: 'svd=@0@'.format(kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME').to_lower()))

peripheral_defs_in = kadoc_proj.get_variable('peripheral_defs_in')
svd_json = kadoc_proj.get_variable('svd_json')
jinja_cli = kadoc_proj.get_variable('jinja_cli')
layout_in = kadoc_proj.get_variable('layout_in')

devicetree_proj = subproject('devicetree', default_options:['install=true'])
dts_in = devicetree_proj.get_variable('devicetree_dts_in')
dts = devicetree_proj.get_variable('devicetree_dtsd')
dts2src = devicetree_proj.get_variable('dts2src')
devicetree_dep = devicetree_proj.get_variable('devicetree_dep')
external_deps += devicetree_dep

# XXX: move to meson-devicetree ?
dtsgen = generator(dts2src,
    arguments: ['-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
    output: '@BASENAME@',
)

# all sources are there, sentry source set is populated in each subdir

with_uapi_opt = get_option('with_uapi')
with_kernel_opt = get_option('with_kernel')
with_idle_opt = get_option('with_idle')
with_doc_opt = get_option('with_doc')
with_autotest = kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
with_tests = get_option('with_tests')
with_tools = get_option('with_tools')
with_proof = get_option('with_proof')
with_sbom_opt = get_option('with_sbom')

if with_idle_opt or with_autotest
    with_uapi_opt = true
endif

# Keep subdir order as-is, do not sort them.
# In order to guanrantee build order and reproducibility,
# Meson **DOES NOT** allow forward build target references by design.
# This also prevent circular dependencies between targets.
#
# Firstly, we need to define arch relative variables.
# and then schema and taskmetadata are required by uapi and kernel.
# UAPI is a dependency for all app/kernel.
# Tasks (idle and autotest) are required to build internal task meta.
# Finally, kernel can be built and then tools that might need some kernel headers.
subdir('support/arch')
subdir('schemas')
subdir('dts')
subdir('uapi')
subdir('idle')
subdir('autotest')
subdir('kernel')
subdir('tools')
subdir('doc')

if with_sbom_opt
  # install python (toolchain) dependencies and kernel build related dependencies
  # to datadir (default being usr/local/share/) at meson install time

  # install python dependencies into sentry-pydeps.json (CycloneDX format)
  cyclonedx_py = find_program('cyclonedx-py', required: false, disabler: true)

  if cyclonedx_py.found()

    fs = import('fs')
    fs.copyfile('requirements.txt')

    cyclonedx_sbom = custom_target(
    output: 'sentry-pydeps.json',
    command: [
        cyclonedx_py,
        'requirements'
    ],
    capture: true,
    build_by_default: true,
    install: true,
    install_dir: get_option('datadir'),
    )
  endif
  # install meson dependencies in meson manifest format, in sentry-deps.json
  meson.install_dependency_manifest(join_paths(get_option('datadir'), 'sentry-deps.json'))

endif

if with_uapi_opt
rust_toolchain = configure_file(
    input: rust_toolchain_in,
    output: '@BASENAME@',
    configuration: rust_toolchain_config,
)
endif

is_experimental = kconfig_data.get('CONFIG_EXPERIMENTAL_MODE', 0)
is_standalone = kconfig_data.get('CONFIG_STANDALONE_MODE', 0)
build_mode = 'Release'
if kconfig_data.get('CONFIG_BUILD_TARGET_RELEASE', 0) != 1
    build_mode = 'Debug'
    warning('!!! This is NOT a release build ! DO NOT USE IT IN PRODUCTION !!!')
endif

summary(
    {
        'soc': kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME').to_lower(),
        'build mode': build_mode,
        'standalone': is_standalone,
        'experimental mode': is_experimental,
        'hardening flags': activated_hardening_cflags,
    },
    bool_yn: true,
    section: 'Configuration'
)

summary(
    {
        'sentry-kernel': with_kernel_opt,
        'idle': with_idle_opt,
        'uapi': with_uapi_opt,
        'autotest': with_autotest,
        'tools': with_tools,
        'doc' : with_doc_opt,
        'unit tests': with_tests,
        'formal proof': with_proof,
        'sbom': with_sbom_opt,
    },
    bool_yn: true,
    section: 'Targets',
)

if with_autotest and not with_tests
# in autotest mode only, fusion all hex into one single hex, to simplify
# gdb flashing. This mode needs srec_cat to fusion all hex into one
# other nominal (debug, release) modes use build system based binary
# generation instead.
srec_cat = find_program('srec_cat', required: false, disabler: true)

if srec_cat.found()
firmware_hex = custom_target(
    depends: [ autotest_hex, idle_hex, sentry_hex ],
    output: 'firmware.hex',
    command: [
        srec_cat,
        '-o', '@OUTPUT@', '-Intel',
        sentry_hex.full_path(), '-Intel',
        idle_hex.full_path(), '-Intel',
        autotest_hex.full_path(), '-Intel',
    ],
    build_by_default: true,
    install: true,
    install_dir: get_option('bindir'),
)
else
warning('srec_cat utility not found!')
warning('!!! Unable to forge final hex automatically! help yourself with ELF and HEX...')
endif

endif

if not with_autotest and not with_tests
# Create an additional single firmware to ease loading in QEMU
srec_cat = find_program('srec_cat', required: false, disabler: true)

if srec_cat.found()
firmware_hex = custom_target(
    depends: [ idle_hex, sentry_hex ],
    output: 'firmware.hex',
    command: [
        srec_cat,
        '-o', '@OUTPUT@', '-Intel',
        sentry_hex.full_path(), '-Intel',
        idle_hex.full_path(), '-Intel',
    ],
    build_by_default: true,
    install: true,
    install_dir: get_option('bindir'),
)
else
warning('srec_cat utility not found!')
warning('!!! Unable to forge final hex automatically! help yourself with ELF and HEX...')
endif

endif
