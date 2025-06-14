// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_STRING_H
#define ZLIB_STRING_H

#include <inttypes.h>
#include <string.h>


/**
 * @fn Sentry specific string functions, exported with their corresponding contracts.
 *
 * At link time, these functions are aliased to the corresponding iso-C symbol, keeping the
 * very same behavior as defined bellow.
 * They do not exactly match the ISO C standard, as they are hardened against null pointer
 * dereferencing. The overall hardened+iso-C compliance is done in the frama-c-zlib-string-wp
 * proof suite.
 */
#ifdef __FRAMAC__
/*@
  axiomatic NullTerminatedString {
    logic boolean has_null_terminator{L}(char *s, integer N);

    // A string of length N has a null terminator between 0 and N-1
    axiom null_terminator_exists:
      \forall char *s, integer N;
        N > 0 ==> has_null_terminator(s, N) <==>
        (\exists integer i; 0 <= i < N && s[i] == '\0');

    // If a string has a null terminator, all indices after the null terminator are irrelevant
    axiom null_terminator_effect:
      \forall char *s, integer N, integer i;
        has_null_terminator(s, N) && 0 <= i < N && s[i] == '\0' ==>
        (\forall integer j; i < j < N ==> s[j] == '\0');
  }
*/
/*@
  axiomatic MemAreasEqual {
    logic boolean memarea_equals{L}(uint8_t *d, uint8_t*s, integer N);

    // Two memory areas matches
    axiom do_matches:
      \forall uint8_t *d, uint8_t *s, integer N;
        N > 0 ==> memarea_equals(d, s, N) <==>
        (\forall integer i; 0 <= i < N && d[i] == s[i]);
  }
*/
/*@
  axiomatic MemAreasSet {
    logic boolean memarea_set{L}(char *d, char C, integer N);

    // Memory area d of len N>0 is set with C
    axiom is_set:
      \forall char* d, integer N, char C;
        N > 0 ==> memarea_set(d, C, N) <==>
        (\forall integer i; 0 <= i < N && d[i] == C);
  }
*/

/*@
   requires s != \null ==> has_null_terminator(s, maxlen);
   terminates \true;
   assigns \nothing;
   ensures s != \null ==> acsl_c_equiv: \result == strnlen(s, maxlen);
   ensures s == \null ==> \result == 0;
  */
size_t sentry_strnlen(const char *s, size_t maxlen);

/*
  Note: using the local implementations contract for proof steps.
  In nominal mode, the corresponding sentry_ prefixed functions are used. This
  allows compsition based proofs that use this contract as valid by hypothesis.
  The effective correctness of below functions contract is made by the test_zlib proof suite.
*/
/*@
  terminates \true;
  exits \false;
  assigns ((uint8_t*)s)[0 .. (n-1)] \from indirect:c, indirect:n;
  assigns \result \from s;
  ensures \result == s;
  */
void   *sentry_memset(void *s, int c, unsigned int n);

/*@
  requires \valid_read((uint8_t*)src + (0 .. n-1)) ==> \initialized((uint8_t*)src + (0 .. n-1));
  terminates \true;
  exits \false;
  assigns ((uint8_t*)dest)[0 .. (n-1)] \from indirect:src, indirect:n;
  assigns \result \from indirect:src, indirect:n;
  // for valid input values, the destination memory must be initalized from src
  ensures
    (\separated((uint8_t*)src + (0 .. n-1), (uint8_t*)dest + (0 .. n-1)) &&
     \valid_read((uint8_t*)src + (0 .. n-1)) &&
     \valid((uint8_t*)dest + (0 .. n-1)))
      ==> memarea_equals((uint8_t*)dest, (uint8_t*)src, n);
  ensures \result == dest;
  */
void   *sentry_memcpy(void * restrict dest, const void* restrict src, size_t n);

/**
 * Note: because frama-c as no link notion and uses cpp+internal analysis, we cannot
 * use the __attribute__((alias("fct"))) trick to alias the sentry_ prefixed
 * functions to the iso-C ones. Instead, we use here cpp-level aliasing that
 * allows to keep the same function name in the proof suite.
 * In production, the sentry_ prefixed functions are aliased to the iso-C (see string.c
 * zlib file).
 * Out of the proof suite, the string.h symbols (ISO C builtins) are used instead, but
 * the linker will resolve the sentry_ prefixed symbols to the iso-C ones.
 */
#define strnlen sentry_strnlen
#define memset sentry_memset
#define memcpy sentry_memcpy

#endif /* __FRAMAC__ */

#endif/*!ZLIB_STRING_H*/
