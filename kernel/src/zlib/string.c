// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <sentry/ktypes.h>

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

/*
 * @brief ISO C equivalent implementation of strnlen
 */
/*@
   requires valid_string_s: valid_read_nstring(s, maxlen);
   assigns \result \from indirect:s, indirect:maxlen;
   ensures acsl_c_equiv: \result == strnlen(s, maxlen);
  */
static inline size_t __sentry_strnlen(const char *s, size_t maxlen)
{
    size_t result = 0;
    /*@
      @ loop invariant 0 <= result <= maxlen;
      @ loop invariant \forall integer i; 0 <= i < result ==> s[i] != '\0';
      @ loop assigns result;
      @ loop variant maxlen - result;
      */
    while ((s[result] != '\0') && result < maxlen) {
        result++;
    }
    /*@ assert \forall integer k; 0 <= k < result ==> s[k] != '\0'; */
    return result;
}

/**
 * @brief hardened implementation of strnlen, checking for null pointer
 * @see __sentry_strnlen() for ISO C equivalent
 */
/*@
   requires s != \null ==> has_null_terminator(s, maxlen);
   assigns \nothing;
   ensures s != \null ==> acsl_c_equiv: \result == strnlen(s, maxlen);
   ensures s == \null ==> \result == 0;
  @*/
#ifndef __FRAMAC__
static
#endif
size_t sentry_strnlen(const char *s, size_t maxlen)
{
    size_t result = 0;

    if (s == NULL) {
        goto err;
    }
    /*@ assert valid_read_nstring(s, maxlen); */
    result = __sentry_strnlen(s, maxlen);
    /*@ assert \forall integer k; 0 <= k < result ==> s[k] != '\0'; */
err:
    return result;
}

/*@
  // ISO C equivalent of memset
  requires n > 0;
  requires (empty_block(s) || \valid((uint8_t*)s + (0 .. n-1)));
  assigns s[0 .. (n-1)] \from indirect:c, indirect:n;
  assigns \result \from s;
  ensures n > 0 ==> memarea_set(s, (char)c, n);
  ensures \result == s;
  */
static inline char * __sentry_memset(char *s, int c, unsigned int n)
{
    /*@ assert \valid(s + (0 .. (n-1))); */
    /*@ assert (c & 0xff) == ((uint8_t)c); */
    /*@ assert \separated(s + (0 .. n-1), (char*)&c); */
    /*@ assert \valid(s + (0 .. (n-1))); */
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop assigns i, s[0 .. (n-1)];
      @ loop variant n - i;
      */
    for (unsigned int i = 0; i < n; i++) {
        /*
         * memseting s with c, keeping internal loop scoping (no border effet).
         * This do not alter the generated asm, as the compiler will optimise this
         */
        /*@ assert 0 <= i < n; */
        /*@ assert ((c & 0xff) == (char)c); */
        s[i] = (c & 0xff);
        /*@ assert s[i] == (char)c; */
    }
err:
    return s;
}

/**
 * @brief Set n first bytes of a given memory area with a given byte value
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior. Here such a case is trapped.
 * The effective behavior conformance is implemented in __sentry_memset().
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
/*@
  assigns ((uint8_t*)s)[0 .. (n-1)] \from indirect:c, indirect:n;
  assigns \result \from s;
  ensures \result == s;
  */
#ifndef __FRAMAC__
static
#endif
void   *sentry_memset(void *s, int c, unsigned int n)
{
    if (unlikely(s == NULL)) {
        goto err;
    }
    if (SIZE_MAX - n < (size_t)s) {
        /* integer overflow avoidance for invalid region definition. Should be dead code here */
        goto err;
    }
    if (unlikely(n == 0)) {
        /* nothing to do, just return */
        goto err;
    }
    /*@ assert \valid((uint8_t*)s + (0 .. (n-1))); */
    s = __sentry_memset((char*)s, c, n);
err:
    return s;
}

/**
 *  auxiliary function that returns SECURE_FALSE if regions
 *  a[0..n-1] and b[0..n-1] do not overlap, or SECURE_TRUE otherwise
 */
/*@
 assigns \nothing;

 behavior same_region:
    assumes a == b;
    ensures \result == SECURE_TRUE;

 behavior null_sized:
 assumes a != b;
   assumes n == 0;
   ensures \result == SECURE_FALSE;

 behavior collision_lt:
  assumes a != b;
  assumes n > 0;
  assumes a < b && (b - a) < n;
  ensures no_eva: \result == SECURE_TRUE;

 behavior collision_gt:
  assumes a != b;
  assumes n > 0;
  assumes b < a && (a - b) < n;
  ensures no_eva: \result == SECURE_TRUE;

 behavior separated_lt:
  assumes a != b;
  assumes n > 0;
  assumes a < b && (b - a) >= n;
  ensures no_eva: \result == SECURE_FALSE;

 behavior separated_gt:
  assumes a != b;
  assumes n > 0;
  assumes b < a && (a - b) >= n;
  ensures no_eva: \result == SECURE_FALSE;

 complete behaviors;
 disjoint behaviors;
*/
static secure_bool_t __regions_overlaps(const size_t a, const size_t b, size_t n)
{
    secure_bool_t res = SECURE_TRUE;

    if (a == b) {
        /* defense in depth, should never happen because of memcpy() preconditions */
        /*@ assert \false; */
        goto err;
    }
    if (n == 0) {
        /* no size, no overlap */
        res = SECURE_FALSE;
        goto err;
    }
    /* integer overflow avoidance when manipulating _b and _a */
    if ((a < b) && ((b - a) < n)) {
        goto err;
    }
    if ((b < a) && ((a - b) < n)) {
        goto err;
    }
    /*@ assert \separated((uint8_t*)a + (0 .. n-1), (uint8_t*)b + (0 .. n-1)); */
    res = SECURE_FALSE;
err:
    return res;
}

/*@
  // ISO C equivalent of memcpy
  requires (empty_block(dest) || \valid(dest+(0..n-1)));
  requires (empty_block(src) || \valid_read(src+(0..n-1)));
  requires \initialized(src+(0..n-1));
  requires separation: \separated(dest+(0..n-1),src+(0..n-1));
  assigns ((uint8_t*)dest)[0 .. (n-1)] \from indirect:src, indirect:n;
  assigns \result \from dest;
  ensures memarea_equals(dest, src, n);
  ensures \separated(\result, src);
  ensures \result == dest;
  */
static inline uint8_t *__sentry_memcpy(uint8_t * restrict dest, const uint8_t* restrict src, size_t n)
{
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall ℤ k; 0 <= k < i ==> dest[k] == src[k];
      @ loop assigns i, dest[0 .. (n-1)];
      @ loop variant n - i;
      */
     for (size_t i = 0; i < n; i++) {
        dest[i] = src[i];
    }
    /*@ assert memarea_equals(dest, src, n); */
    return dest;
}

 /*
  * @brief Copy n first bytes from src to dest
  *
  * INFO: The C standard says that null argument(s) to string
  * functions produce undefined behavior.Here such a case is trapped.
  * The effective behavior conformance is implemented in __sentry_memcpy().
  *
  * This is a global warning for the POSIX and C99/C99 libstring:
  * check your arguments before using it!
  *
  * Conforming to:
  * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
  */
/*@
  requires \valid_read((uint8_t*)src + (0 .. n-1)) ==> \initialized((uint8_t*)src + (0 .. n-1));
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
#ifndef __FRAMAC__
static
#endif
void   *sentry_memcpy(void * restrict dest, const void* restrict src, size_t n)
{
    if (unlikely(dest == NULL || src == NULL)) {
        goto err;
    }
    /*@ assert \valid((uint8_t*)dest + (0 .. (n-1))); */
    /*@ assert \valid_read((uint8_t*)src + (0 .. (n-1))); */
    if (unlikely(__regions_overlaps((size_t)dest, (size_t)src, n) == SECURE_TRUE)) {
        goto err;
    }

    /*@ assert \separated((uint8_t*)dest + (0 .. n-1), (uint8_t*)src + (0 .. n-1)); */
    /*@ assert \valid((uint8_t*)dest + (0 .. (n-1))); */
    /*@ assert \valid_read((uint8_t*)dest + (0 .. (n-1))); */
    /*@ assert \initialized((uint8_t*)src+(0..n-1)); */
    __sentry_memcpy(dest, src, n);
    /*@ assert \forall integer k; 0 <= k < n ==> ((uint8_t*)dest)[k] == ((uint8_t*)src)[k]; */
err:
    return dest;
}

#ifndef TEST_MODE
#ifndef __FRAMAC__
/** NOTE: FramaC requires that we use its own compiler builtins (see -eva-builtins-list for more info) */
/* if not in the test suite case, aliasing to POSIX symbols, standard string.h header can be added */
size_t strnlen(const char *s, size_t maxlen) __attribute__((alias("sentry_strnlen")));
void* memset(void *s, int c, unsigned int n) __attribute__((alias("sentry_memset")));
void* memcpy(void * restrict d, const void * restrict s, size_t) __attribute__((alias("sentry_memcpy")));
#endif
#endif/*!TEST_MODE*/
