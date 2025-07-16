// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_SORT_H
#define ZLIB_SORT_H

#include <inttypes.h>
#include <sentry/ktypes.h>
#include <sentry/zlib/string.h>

/** \addtogroup sort
 *  @{
 */

/**
 * @def sort swap function prototype
 *
 * If the caller need a specific swap function, it must respect the following
 * prototype.
 * @param a[out]: first cell to swap
 * @param b[out]: second cell to swap
 * @param size[in]: cell size in bytes
 */
typedef void (*swap_func_t)(void *a, void *b, size_t size);

/**
 * @def sort compare function prototype
 *
 * Always required. Specify the way to compare a and b
 *
 * @param a[in]: first cell to compare
 * @param b[in]: second cell to compare
 *
 * @returns:
 *   A positive value if a is bigger than b, a negative value if
 *   a is smaller than b, or 0 if they are equal
 */
typedef int (*cmp_func_t)(const void *a, const void *b);

/*@

    requires \separated((uint8_t*)a + (0 .. size-1), (uint8_t*)b + (0 .. size-1));
    requires \valid((uint8_t*)a + (0 .. size-1));
    requires \valid((uint8_t*)b + (0 .. size-1));
    requires \initialized((uint8_t*)a + (0 .. size-1));
    requires \initialized((uint8_t*)b + (0 .. size-1));
    requires size_valid: size > 0;
    assigns ((uint8_t*)a)[0 .. size-1], ((uint8_t*)b)[0 .. size-1];
    // functional correctness of the swap notion
    ensures \forall integer i; 0 <= i < size ==>
     ((uint8_t*)a)[i] == \old(((uint8_t*)b)[i]) && ((uint8_t*)b)[i] == \old(((uint8_t*)a)[i]);
*/
/**
 * @brief generic swap function
 *
 * This function swaps the contents of two memory areas of the same size.
 * It is designed to be used when a specific swap function is not provided.
 * It uses a temporary buffer to hold the contents of one area while
 * performing the swap.
 *
 * @param a[out]: pointer to the first memory area to swap
 * @param b[out]: pointer to the second memory area to swap
 * @param size[in]: size of the memory areas in bytes
 *
 */
static inline void generic_swap(void * restrict a, void * restrict b, size_t size)
{
    /**
     * this implementation is stack consumming, but cycle efficient. Wey may use instead
     * a per-cell swap.
     *
     * NOTE: once using C23 instead of C11, the a and b types should also be validated
     * using static_assert() on typeof() to ensure that they are homogeneous
     */
    uint8_t buf[size];
    memcpy(&buf[0], b, size);
    /*@ assert \forall integer i; 0 <= i < size ==> buf[i] == ((uint8_t*)b)[i]; */
    memcpy(b, a, size);
    /*@ assert \forall integer i; 0 <= i < size ==> ((uint8_t*)b)[i] == ((uint8_t*)a)[i]; */
    memcpy(a, &buf[0], size);
    /*@ assert \forall integer i; 0 <= i < size ==> ((uint8_t*)a)[i] == ((uint8_t*)buf)[i]; */
}

/**
 * @brief simple, yet generic, bubble sort for all kernel tables
 *
 * @param table[out]: the table to sort
 * @param len[in]: number of cells in the table
 * @param cell_size[in]: size of a cell in bytes
 * @param cmp[in]: comparison function, required
 * @param swp[in]: swap function. If NULL, fallback to generic_swap
 */
/*@
  requires table_valid: table != \null;
  requires table != \null ==> \valid((uint8_t*)table + (0 .. len*cell_size-1));
  requires \valid_function(cmp);
  requires cell_size_valid: cell_size > 0;
  requires len_valid: len == 0 || \valid((uint8_t*)table + (0 .. len*cell_size-1));
  requires swap_valid: swp == \null || \valid_function(swp);

  assigns ((uint8_t*)table)[0 .. len*cell_size-1];
  ensures len < 2 ==> \result == K_STATUS_OKAY;
  ensures \result == K_STATUS_OKAY || \result == K_ERROR_INVPARAM;
*/
static inline kstatus_t bubble_sort(void * restrict table, size_t len, size_t cell_size, cmp_func_t cmp, swap_func_t swp)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(table == NULL || cmp == NULL)) {
        /* defense in depth */
        /*@ assert \false; */
        goto end;
    }
    if (unlikely(len < 2 || cell_size == 0)) {
        status = K_STATUS_OKAY;
        /* nothing to be done */
        goto end;
    }
    /*@ assert \valid((uint8_t*)table + (0 .. len*cell_size-1)); */
    if (swp == NULL) {
        swp = generic_swap;
    }
    /*@ assert \valid_function(swp); */
    /*@
      loop invariant 0 <= i < len;
      loop assigns i, ((uint8_t*)table)[0 .. len*cell_size-1];
      loop variant len - i;
    */
    for (size_t i = 0; i < len; i++) {
        /*@
          loop invariant 0 <= j < len;
          loop assigns j, ((uint8_t*)table)[0 .. len*cell_size-1];
          loop variant len - i;
          */
        for (size_t j = 0; j < len - 1 - i; j++) {
            size_t ta = (size_t)table + (j*cell_size);
            size_t tb = (size_t)table + ((j+1)*cell_size);
            if (cmp((void*)ta, (void*)tb) > 0) {
                swp((void*)ta, (void*)tb, cell_size);
            }
        }
    }
    status = K_STATUS_OKAY;
end:
    return status;
}


/** \addtogroup sort
 *  @}
 */


#endif/*!ZLIB_SORT_H*/
