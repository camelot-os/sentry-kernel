# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0
#
## kernel code include both its own headers and UAPI headers
kernel_inc = include_directories(
    'include',
    '../uapi/include'
)

# while kernel inc are required for externals (tools), if kernel build
# is not required, stop here
if not with_kernel_opt
    subdir_done()
endif

if meson.is_subproject()
warning('!!! Are you sure you want to build the Sentry kernel as a subproject ?')
endif

# potential overriden link-time arguments, for e.g. if adding e-ACSL and symbols substitution in
# various kernel libraries. Defaulting to empty list.
target_link_args = []

# sources, generated and effective
sentry_header_set = ssmod.source_set()
sentry_header_set.add(kconfig_h)

sentry_linker_script = files()
sentry_linker_script_path = files()

# populated in src
sentry_ldscript_template = files()

sentry_dts_file = fs.name(dts_in)
sentry_dts_args = '-DDTS_FILE="@0@"'.format(sentry_dts_file)

# sentry header set is populated in the include dir
# BSP is driver related headers. Drivers exported header are only used by
# managers. As such, there should not have <bsp/xx> path out of the managers
# source directory.
subdir('include/bsp')
# kernel-wide exported headers
subdir('include/sentry')

sentry_header_set_config = sentry_header_set.apply(kconfig_data, strict: false)

subdir('src')

# there is no mean in building a target ELF file with coverage functions added.
# It will not fit in target, and it will not be usable as is.
if with_kernel_opt and not with_tests
# XXX:
# For ldscript gen we use a custom target instead of the previously defined
# generator as we need to know the outputed filename at link time
# (FYI generator generates anonymous file that can be built bu we can't use
# the generated filename in any other target)
sentry_ldscript = custom_target('sentry_ldscript',
    input: sentry_ldscript_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

sentry_linker_args = [
    '-T@0@'.format(sentry_ldscript.full_path()),
    '-z', 'noexecstack',
]

sentry_map_file = '@0@.map'.format(meson.project_name())


sentry_elf = executable(
    meson.project_name(),
    name_suffix: 'elf',
    sources: [
        sentry_startup,
        sentry_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    dependencies: [
        sentry_arch_dep,
        sentry_zlib_dep,
        sentry_bsp_dep,
        sentry_sched_dep,
        sentry_managers_dep,
        sentry_syscall_dep,
        external_deps
    ],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    link_args: [
        target_link_args,
        '-lgcc',
        target_arch_args,
        sentry_linker_args,
        '-Wl,-Map=@0@'.format(sentry_map_file),
    ],
    link_language: 'c',
    link_depends: [ sentry_ldscript ],
    install: true,
)

sentry_hex = custom_target(
    input: sentry_elf,
    output: '@BASENAME@.hex',
    command: [
        objcopy,
        '-O', 'ihex',
        '@INPUT@',
        '@OUTPUT@'
    ],
    install: true,
    install_dir: get_option('bindir'),
)

sentry_bin = custom_target(
    input: sentry_elf,
    output: '@BASENAME@.bin',
    command: [objcopy, '--output-target=binary', '@INPUT@', '@OUTPUT@'],
    install: true,
    install_dir: get_option('bindir'),
    install_tag: 'runtime',
)

if kconfig_data.get('CONFIG_WITH_UF2', 0) == 1
picotool = find_program('picotool', required: true)

custom_target(
    input: sentry_bin,
    output: '@BASENAME@.uf2',
    command: [
        picotool, 'uf2',
        'convert', '@INPUT@', '-t', 'bin',
        '@OUTPUT@', '-t', 'uf2'
    ],
    install: true,
    install_dir: get_option('bindir'),
    install_tag: 'runtime',
)
endif

meson.add_install_script(sentry_install_script, sentry_map_file, get_option('infodir') / meson.project_name())

endif

if with_tests
    subdir('tests')
endif

if with_proof
  subdir('proof')
endif
