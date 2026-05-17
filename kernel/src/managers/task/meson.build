# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# main kernel-relative content
managers_source_set.add(files(
  'task_init.c',
  'task_core.c',
  'task_idle.c',
  'task_respawn.c',
))

if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
task_autotest_template = files('task_autotest.c.in')

task_autotest = custom_target('gen_task_autotest',
  input: task_autotest_template,
  output: '@BASENAME@',
  depends: [ autotest_json ],
  command: [ jinja_cli, '-d', autotest_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

managers_source_set.add(task_autotest)
endif
