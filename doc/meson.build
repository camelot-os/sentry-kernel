# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if not with_doc_opt
    subdir_done()
endif

pymod = import('python')
sphinx = find_program('sphinx-build')
doxygen = find_program('doxygen')

py3 = pymod.find_installation(
    'python3',
    modules: [
        'exhale',
        'sphinx_rtd_theme',
        'sphinx_simplepdf',
    ]
    )

# man pages sources
subdir('concepts/uapi/syscalls')

# used by sphinx_simplepdf
weasyprint = find_program('weasyprint', required: true)

concepts_rst = files(
    'concepts/_static/figures/svc_exchange.png',
    'concepts/_static/figures/sentry_kernel.png',
    'concepts/_static/figures/dts_in_drivers.png',
    'concepts/_static/figures/waiting_events.png',
    'concepts/_static/figures/system_sw_layout.png',
    'concepts/_static/figures/rrmq.png',
    'concepts/_static/figures/svd_in_drivers.png',
    'concepts/_static/figures/managers.png',
    'concepts/_static/figures/deadlock.png',
    'concepts/_static/figures/capabilities.png',
    'concepts/_static/figures/camelot_fp.png',
    'concepts/_static/figures/autotest_mgr.png',
    'concepts/_static/figures/camelot.png',
    'concepts/_static/figures/managers.mermaid',
    'concepts/_static/figures/task_mapping.png',
    'concepts/_static/figures/user_irq_automaton.png',
    'concepts/_static/figures/camelot.ico',
    'concepts/build_system/targets.rst',
    'concepts/build_system/svd.rst',
    'concepts/build_system/index.rst',
    'concepts/build_system/dts.rst',
    'concepts/conf.py',
    'concepts/concepts/archi_req.rst',
    'concepts/concepts/events.rst',
    'concepts/concepts/security.rst',
    'concepts/concepts/events.rst',
    'concepts/concepts/index.rst',
    'concepts/concepts/initial.rst',
    'concepts/index.rst',
    'concepts/uapi/index.rst',
    'concepts/uapi/model.rst',
    'concepts/uapi/syscalls.rst',
    'concepts/sw_architecture/bsp.rst',
    'concepts/sw_architecture/schedulers.rst',
    'concepts/sw_architecture/task_layout.rst',
    'concepts/sw_architecture/index.rst',
    'concepts/sw_architecture/user_devices.rst',
    'concepts/tests/autotest.rst',
    'concepts/tests/index.rst',
    'concepts/tests/unittests.rst',
    'concepts/proof/index.rst',
    'concepts/proof/basics.rst',
    'concepts/proof/eva.rst',
    'concepts/proof/wp.rst',
)

concepts_rst += syscalls_src

concepts = custom_target('doc-concepts',
    input: concepts_rst,
    depend_files: [files('concepts/conf.py')],
    output: 'concepts',
    install: true,
    install_tag: 'doc',
    install_dir: get_option('datadir') / 'doc/sentry-kernel',
    command: [sphinx, '-b', 'html', '-q', '-d',
        'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'concepts'),
        'doc/concepts',
    ])
doc_concepts = alias_target('doc-concepts', concepts)

concepts_singlehtml = custom_target('doc-concepts-singlehtml',
    input: concepts_rst,
    depend_files: [files('concepts/conf.py')],
    output: 'concepts_singlehtml',
    command: [sphinx, '-b', 'singlehtml', '-q', '-d',
        'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'concepts'),
        'doc/concepts_singlehtml',
    ])
doc_concepts_singlehtml = alias_target('doc-concepts-singlehtml', concepts_singlehtml)


concepts_pdf = custom_target('doc-concepts-pdf',
    input: concepts_rst,
    depend_files: [files('concepts/conf.py')],
    output: 'concepts_pdf',
    command: [sphinx, '-b', 'simplepdf', '-q',
        '-d', 'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'concepts'),
        'doc/concepts_pdf',
    ])
doc_concepts_pdf = alias_target('doc-concepts-pdf', concepts_pdf)

internals_rst = files(
    'internals/_static/figures/camelot.ico',
    'internals/_static/figures/camelot.png',
    'internals/conf.py',
    'internals/Doxyfile',
    'internals/index.rst',
)
internals = custom_target('doc-internals',
    input: internals_rst,
    depend_files: [files('internals/conf.py')],
    output: 'internals',
    command: [sphinx, '-b', 'html', '-q', '-d',
        'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'internals'),
        'doc/internals',
    ])
doc_internals = alias_target('doc-internals', internals)

doc = alias_target(
    'doc',
    concepts,
    internals,
)

# man pages target
subdir('mans')
