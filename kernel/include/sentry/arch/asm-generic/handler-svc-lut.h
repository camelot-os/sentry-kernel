// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-FileCopyrightText: 2025 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLER_LUT_H
#define HANDLER_LUT_H

/**
 * @file SVC entrypoint syscalls lookuptable, avoiding unefficient long switch case, using
 * syscall identifier as LUT index.
 * gate indirection is arch-generic, and keeps SVC handler performance in O(1)
 */

typedef stack_frame_t* (*lut_svc_handler)(stack_frame_t *);

lut_svc_handler const *svc_lut_get(void);

size_t svc_lut_size(void);

stack_frame_t *lut_unsuported(stack_frame_t *frame);

#endif/*!HANDLER_LUT_H*/
