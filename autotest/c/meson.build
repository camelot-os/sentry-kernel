# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

ssmod = import('sourceset')

userspace_args = [
    '-fstack-protector-strong',
    '-Wconversion',
]

# populated in src
autotest_sourceset = ssmod.source_set()
autotest_headerset = ssmod.source_set()

subdir('include')
subdir('src')

autotest_sources = autotest_sourceset.apply(kconfig_data, strict: false).sources()
autotest_headers = autotest_headerset.apply(kconfig_data, strict: false).sources()

uapi_inc = include_directories('../../uapi/include')

autotest_elf = executable(
    autotest_task_name,
    name_suffix: 'elf',
    sources: [ autotest_sources, autotest_headers ],
    include_directories: [ uapi_inc, autotest_inc ],
    dependencies: [ autotest_test_dep ],
    c_args: [ target_arch_args, global_build_args, userspace_args ],
    link_args: [ '-lgcc', target_arch_args, autotest_linker_args, '-Wl,-Map=@0@'.format(autotest_map_file)],
    link_language: 'c',
    link_depends: [ autotest_ldscript ],
    install: true,
)
