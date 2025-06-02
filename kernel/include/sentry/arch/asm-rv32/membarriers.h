// SPDX-FileCopyrightText: 2025 ANSSI
// SPDX-License-Identifier: Apache-2.0

#ifndef __MEMBARRIERS_H_
#define __MEMBARRIERS_H_

#include <inttypes.h>
#include <stdbool.h>

// TODO : improve use of fence

/**
 * @brief Compiler barrier
 *
 * This barrier does not produce any binary code.
 * It prevents compiler to re-order load/store
 */
/*@
  assigns \nothing;
 */
inline __attribute__((always_inline)) void arch_barrier(void) {
#ifndef __FRAMAC__
    asm volatile ("" ::: "memory");
#endif
}

/**
 * @brief Processor memory barrier
 *
 * This barrier prevents processor to re-order load/store after this barrier
 */
/*@
	assigns \nothing;
*/
inline __attribute__((always_inline)) void arch_data_mem_barrier(void) {
#ifndef __FRAMAC__
    asm volatile ("fence");
#endif
}


/*
 * Make sure that any explicit data memory transfer specified before is done before the
 * next instruction (harder than previous case, but slower).
 */

/**
 * @brief Processor memory synchronisation barrier
 *
 * This barrier wait for all previous memory access to be done before continue
 * execution.
 */
/*@
  assigns \nothing;
 */
inline __attribute__((always_inline)) void arch_data_sync_barrier(void) {
#ifndef __FRAMAC__
    asm volatile ("fence");
#endif
}

/**
 * @brief Processor instruction synchronisation barrier
 *
 * This barrier will discard all further prefetched instruction
 * This is needed after enabling an isr, context task switch, etc.
 */
/*@
  assigns \nothing;
 */
inline __attribute__((always_inline)) void arch_inst_sync_barrier(void) {
#ifndef __FRAMAC__
    asm volatile ("fence");
#endif
}

/* INFO:
 * backend membarrier asm inline is not executed in FramaC context, because asm inline
 * generates uncontroled peace of code that makes proof problem (assigns are no more
 * validated as asm inline can't be evaluated).
 * As this peace of code is very small (calling dmb instructions) we consider, using a
 * manual review, that there is **no** border effect generating potential RTE or invalid
 * assignation there.
 */

/*
 * These functions permits to ensure that target data are written back in memory before
 * the next instruction happens. This avoid optimization side-effects (typically register
 * caching) when concurrent threads share a given variable.
 *
 * CAUTION: these functions permits to ensure that the given variables (scalar, atomically written
 * in memory (reduced to 32bit scalar types and smaller ones) are correctly pushed back in memory
 * in order to be consistent in the case of a separately threaded (concurrent) accessor.
 *
 * These functions DOES NOT protect consistency for non-atomic types (structures or any type that
 * are *not* atomically written in the corresponding hardware datasheet.
 * To resolve this problematic, please use mutexes and semaphores. In the same way, mutexes and
 * semaphore *does not* protect against compiler optimization and memory barriers myst be used
 * in addition.
 */

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline __attribute__((always_inline)) void set_u8_with_membarrier(uint8_t *target, uint8_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_mem_barrier();
#endif
}

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline __attribute__((always_inline)) void set_u16_with_membarrier(uint16_t *target, uint16_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_mem_barrier();
#endif
}

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline __attribute__((always_inline)) void set_u32_with_membarrier(uint32_t *target, uint32_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_mem_barrier();
#endif
}

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline __attribute__((always_inline)) void set_bool_with_membarrier(bool *target, bool val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_mem_barrier();
#endif
}

/*@
  @ assigns \nothing;
*/
inline __attribute__((always_inline)) void request_data_membarrier(void) {
#ifndef __FRAMAC__
    arch_data_mem_barrier();
#endif
}

#endif/*__MEMBARRIERS_H_*/
