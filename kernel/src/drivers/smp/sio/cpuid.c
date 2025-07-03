// SPDX-FileCopyrightText: 2025 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#include <sentry/ktypes.h>
#include <bsp/drivers/smp/smp.h>
#include <sentry/io.h>
#include "sio_private.h"

/* no init required for CPUID IP */

/* reading the CPUID never fails on RP2350 */
/*@
  requires \valid(cpuid);
  assigns(*cpuid);
 */
kstatus_t sio_get_cpuid(size_t * const cpuid)
{
    kstatus_t res = K_ERROR_INVPARAM;
    if (unlikely(cpuid == NULL)) {
        /* defense in depth, should be deadcode */
        /*@ assert \false; */
        goto err;
    }
    *cpuid = ioread32(SIO_CPUID_REG);
    res = K_STATUS_OKAY;
err:
    return res;
}

/* exported SoC generic SMP API */
kstatus_t smp_get_cpuid(size_t * const cpuid) __attribute__((alias("sio_get_cpuid")));
