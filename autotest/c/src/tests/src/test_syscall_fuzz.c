// SPDX-FileCopyrightText: 2026 H2Lab OSS Team
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>

#include <syscall_fuzz.h>
#include <test_log.h>
#include <uapi/platform.h>
#include <uapi/types.h>
#include <uapi/uapi.h>

#include "test_syscall_fuzz.h"

#define FUZZ_SYSCALL_SEND_IPC_ID 11U
#define FUZZ_SYSCALL_INVALID_ID  255U

_Static_assert(FUZZ_SYSCALL_SEND_IPC_ID == SYSCALL_SEND_IPC, "syscall id mismatch");

#ifndef CONFIG_TEST_SYSCALL_FUZZ_ITERS
#define CONFIG_TEST_SYSCALL_FUZZ_ITERS 512U
#endif

#define FUZZ_ASSERT_STATUS(got, expected) do {                                   \
    if ((got) != (expected)) {                                                   \
        failure_int(__func__, __LINE__, "!=", (int)(got), (int)(expected));     \
    } else {                                                                      \
        success_int(__func__, __LINE__, "==", (int)(got), (int)(expected));     \
    }                                                                             \
} while (0)

static inline uint32_t fuzz_prng_next(uint32_t *state)
{
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

static void fuzz_invalid_syscall_path(void)
{
    TEST_START();

    for (uint32_t i = 0; i < 64U; ++i) {
        Status st = raw_sys_invalid_255();
        FUZZ_ASSERT_STATUS(st, STATUS_NO_ENTITY);
    }

    LOG("[FUZZ][SUMMARY] invalid_syscall id=%u iters=64 status=stable", FUZZ_SYSCALL_INVALID_ID);
    TEST_END();
}

static void fuzz_ipc_len_truncation_path(void)
{
    Status st;
    taskh_t myself = 0;
    uint32_t rng = 0xC0FFEE5AU;
    uint8_t rxbuf[SENTRY_SVCEXCHANGE_LEN] = {0};
    uint8_t txbuf[SENTRY_SVCEXCHANGE_LEN] = {0};

    uint32_t attempts = 0;
    uint32_t invalid_count = 0;
    uint32_t ok_count = 0;
    uint32_t truncation_hits = 0;
    uint32_t wait_error_count = 0;

    st = __sys_get_process_handle(0xbabeUL);
    FUZZ_ASSERT_STATUS(st, STATUS_OK);
    st = copy_from_kernel((uint8_t *)&myself, sizeof(myself));
    FUZZ_ASSERT_STATUS(st, STATUS_OK);

    for (size_t i = 0; i < sizeof(txbuf); ++i) {
        txbuf[i] = (uint8_t)(i & 0xffU);
    }

    TEST_START();

    for (uint32_t i = 0; i < CONFIG_TEST_SYSCALL_FUZZ_ITERS; ++i) {
        uint32_t fuzzed_len;
        size_t max_copy;
        exchange_event_t *evt;

        /*
         * Bias around interesting boundaries:
         * - [0..511] hits u8 truncation border and SVC max border in one stream.
         */
        fuzzed_len = fuzz_prng_next(&rng) & 0x1ffU;
        max_copy = (fuzzed_len < SENTRY_SVCEXCHANGE_LEN)
            ? (size_t)fuzzed_len
            : (size_t)SENTRY_SVCEXCHANGE_LEN;

        st = copy_to_kernel(txbuf, max_copy);
        FUZZ_ASSERT_STATUS(st, STATUS_OK);

        attempts++;
        st = raw_sys_send_ipc_u32(myself, fuzzed_len);

        if (fuzzed_len > (SENTRY_SVCEXCHANGE_LEN - sizeof(exchange_event_t))) {
            FUZZ_ASSERT_STATUS(st, STATUS_INVALID);
            invalid_count++;
            continue;
        }

        if (st != STATUS_OK) {
            LOG("[FUZZ][WARN] send_ipc returned unexpected status=%d len=%lu", st, fuzzed_len);
            continue;
        }

        ok_count++;

        st = __sys_wait_for_event(EVENT_TYPE_IPC, 100);
        if (st != STATUS_OK) {
            wait_error_count++;
            LOG("[FUZZ][WARN] wait_for_event failed status=%d len=%lu", st, fuzzed_len);
            continue;
        }

        st = copy_from_kernel(rxbuf, SENTRY_SVCEXCHANGE_LEN);
        FUZZ_ASSERT_STATUS(st, STATUS_OK);

        evt = (exchange_event_t *)&rxbuf[0];

        if ((fuzzed_len > 255U) && (evt->length != (uint8_t)fuzzed_len)) {
            LOG("[FUZZ][WARN] inconsistent truncation len=%lu evt_len=%u", fuzzed_len, evt->length);
        }

        if ((fuzzed_len > 255U) && (evt->length == (uint8_t)fuzzed_len)) {
            truncation_hits++;
            LOG("[FUZZ][RISK] IPC_TRUNCATION len_in=%lu len_seen=%u", fuzzed_len, evt->length);
        }
    }

    LOG("[FUZZ][SUMMARY] ipc_len attempts=%lu ok=%lu invalid=%lu trunc_hits=%lu wait_errors=%lu",
        attempts,
        ok_count,
        invalid_count,
        truncation_hits,
        wait_error_count);

    TEST_END();
}

void test_syscall_fuzz(void)
{
    TEST_SUITE_START("syscall_fuzz");

    fuzz_invalid_syscall_path();
    fuzz_ipc_len_truncation_path();

    TEST_SUITE_END("syscall_fuzz");
}
