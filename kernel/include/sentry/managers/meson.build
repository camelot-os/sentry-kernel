# SPDX-FileCopyrightText: 2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

managers_header_set = ssmod.source_set()

managers_header_set.add(files(
  'clock.h',
  'debug.h',
  'device.h',
  'interrupt.h',
  'io.h',
  'memory_types.h',
  'memory.h',
  'security.h',
  'task.h',
  'time.h',
))

task_metadata_h = custom_target('task_metadata_h',
    input: files('task_metadata.h.in'),
    output: '@BASENAME@',
    depend_files: [ task_metadata_json ],
    command: [ jinja_cli, '-d', task_metadata_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

capability_h = custom_target('capability_h',
    input: files('capability.h.in'),
    output: '@BASENAME@',
    depend_files: [ task_capabilities_json ],
    command: [ jinja_cli, '-d', task_capabilities_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

managers_header_set.add(task_metadata_h, capability_h)

managers_header_set_config = managers_header_set.apply(kconfig_data, strict:false)
