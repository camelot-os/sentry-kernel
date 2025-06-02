# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

arch_source_set.add(files(
  'nvic.c',
  'thread.c',
  'systick.c',
  'tick.c',
  'semihosting.c',
  'handler.c',
  'handler-svc-lut.c',
))

# VTOR and handlers are not a part of the library, but instead hold in the
# core kernel ELF generation.
# The same rule is used for ldscripts, which have no meaning in library build

sentry_vtor_template = files('vtor.c.in')

sentry_vtor_c = custom_target('gen_vtor',
  input: sentry_vtor_template,
  output: '@BASENAME@',
  depends: [ svd_json ],
  command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

arch_source_set.add(sentry_vtor_c.to_list())


if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
# adding autotest app sections to ldscript. autotest specific
sentry_ldscript_template = files('cortex-m-sentry-autotest.ld.in')
else
sentry_ldscript_template = files('cortex-m-sentry.ld.in')
endif
