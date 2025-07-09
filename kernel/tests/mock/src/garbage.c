// SPDX-FileCopyrightText: 2025 Camelot OSS team
// SPDX-License-Identifier: Apache-2.0

#include <stdlib.h>
#include <time.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <sentry/ktypes.h>

static bool seeded = false;

void get_garbage_u32(uint32_t *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    *rng = (uint32_t)(rand()%__UINT32_MAX__);
}

void get_garbage_u16(uint16_t *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    *rng = (uint16_t)(rand()%__UINT16_MAX__);
}

void get_garbage_u8(uint8_t *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    *rng = (uint8_t)(rand()%__UINT8_MAX__);
}

void get_garbage_ul(unsigned long *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    *rng = (unsigned long)(rand()%__LONG_MAX__);
}

void get_garbage_ull(unsigned long long *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    /* considering tests are executed on 64 bits archi */
    *rng = (unsigned long)(rand()%__LONG_MAX__);
    if (sizeof(rng) == 8) {
        *rng  = *rng << 32;
        *rng += (unsigned long)(rand()%__LONG_MAX__);
    }
}

void get_garbage_l(long *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    *rng = (long)(rand()%__LONG_MAX__);
}

void get_garbage_i(int *rng)
{
    if (unlikely(seeded == false)) {
        srand(time(NULL));
    }
    assert(rng != NULL);
    *rng = (long)(rand()%__INT_MAX__);
}
