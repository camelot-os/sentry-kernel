// SPDX-FileCopyrightText: 2025 H2Lab
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <framac_entropy.h>
#include <sentry/zlib/sort.h>

/*@
    requires \valid((uint8_t*)a);
    requires \valid((uint8_t*)b);
    requires \initialized((uint8_t*)a);
    requires \initialized((uint8_t*)b);
    assigns \nothing;
    ensures a > b <==> \result > 0;
    ensures a < b <==> \result < 0;
    ensures a == b <==> \result == 0;
 */
static int cmp_u8(const void *a, const void *b)
{
    /*@ assert \valid((uint8_t*)a) && \valid((uint8_t*)b); */
    /*@ assert \initialized((uint8_t*)a) && \initialized((uint8_t*)b); */
    return (*(const uint8_t *)a - *(const uint8_t *)b);
}


/*@
    requires valid_cmp: \valid_function(cmp);
    requires valid_swp: swp == \null || \valid_function(swp);
    requires cell_size_valid: cell_size > 0;
*/
static void do_sort(size_t cell_size, cmp_func_t cmp, swap_func_t swp)
{
    uint8_t src[128];
    volatile uint8_t val = 0;
    /* initilizing src with garbaged (unpredictable) values */
    /*@
      loop invariant 0 <= i <= 128;
      loop assigns i, src[0 .. 127];
      loop variant 128 - i;
     */
    for (size_t i = 0; i < 128; ++i) {
        src[i] = val;
    }
    /* testing sort.h API */
    bubble_sort(src, 128, sizeof(uint8_t), cmp, swp);
}

/*@ assigns \nothing; */
void kernel_zlib(void)
{
    uint32_t res;

    do_sort(sizeof(uint8_t), cmp_u8, NULL);
}
