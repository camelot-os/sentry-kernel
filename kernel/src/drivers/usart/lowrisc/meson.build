# SPDX-FileCopyrightText: 2025 ANSSI
# SPDX-License-Identifier: Apache-2.0

uart_template_h = files('opentitan_uart.h.in')

uart_h = dtsgen.process(uart_template_h)

bsp_source_set.add(files('opentitan_uart.c'))

bsp_private_gen_header_set.add(uart_h)
