// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <sentry/ktypes.h>

/* string related functions, for debug usage only */
/*@ requires valid_string_s: valid_read_nstring(s, maxlen);
  @ assigns \result;
  @ ensures result_bounded: \result == strlen(s) || \result == maxlen;
  @*/
#ifndef __FRAMAC__
static
#endif
size_t sentry_strnlen(const char *s, size_t maxlen)
{
    size_t result = 0;

    if (s == NULL) {
        /* should never happen based on subprogram contract */
        /*@ assert \false; */
        goto err;
    }
    /*@
      @ loop invariant 0 <= result <= maxlen;
      @ loop invariant \forall integer i; 0 <= i < result ==> s[i] != '\0';
      @ loop assigns result;
      @ loop variant maxlen - result;
      */
    while ((s[result] != '\0') && result < maxlen) {
        result++;
    }
err:
    return result;
}

/*@
  // ISO C equivalent of memset
  requires \valid((uint8_t*)s + (0 .. n-1));
  assigns ((uint8_t*)s)[0 .. (n-1)] \from c;
  assigns \result \from s, indirect:c, indirect:n;
  ensures acsl_c_equiv: memset((char*)s,c,n);
  ensures \forall integer i; 0 <= i < n ==> ((uint8_t*)s)[i] == (uint8_t)c;
  ensures \result == s;
  */
static inline unsigned char * __sentry_memset(unsigned char *s, int c, unsigned int n)
{
    /*@ assert \valid((uint8_t*)s + (0 .. (n-1))); */
    /*@ assert (c & 0xff) == ((uint8_t)c); */
    /*@ assert \separated((uint8_t*)s + (0 .. n-1), (uint8_t*)&c); */
    /*@ assert \valid((uint8_t*)s + (0 .. (n-1))); */
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop assigns i, ((uint8_t*)s)[0 .. (n-1)];
      @ loop variant n - i;
      */
    for (unsigned int i = 0; i < n; i++) {
        /*
         * memseting s with c, keeping internal loop scoping (no border effet).
         * This do not alter the generated asm, as the compiler will optimise this
         */
        /*@ assert 0 <= i < n; */
        /*@ assert (c & 0xff) == ((uint8_t)c); */
        ((uint8_t * const)s)[i] = (c & 0xff);
        /*@ assert ((uint8_t *)s)[i] == (uint8_t)c; */
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
  assigns ((uint8_t*)s)[0 .. (n-1)];
  assigns \result \from s, indirect:c, indirect:n;
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
    if (n == 0) {
        /* nothing to do, return the pointer */
        goto err;
    }
    if (SIZE_MAX - n < (size_t)s) {
        /* integer overflow avoidance for invalid region definition. Should be dead code here */
        goto err;
    }
    /*@ assert \valid((uint8_t*)s + (0 .. (n-1))); */
    s = __sentry_memset((uint8_t*)s, c, n);
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
  ensures \result == SECURE_TRUE;

 behavior collision_gt:
  assumes a != b;
  assumes n > 0;
  assumes b < a && (a - b) < n;
  ensures \result == SECURE_TRUE;

 behavior separated_lt:
  assumes a != b;
  assumes n > 0;
  assumes a < b && (b - a) >= n;
  ensures \result == SECURE_FALSE;

 behavior separated_gt:
  assumes a != b;
  assumes n > 0;
  assumes b < a && (a - b) >= n;
  ensures \result == SECURE_FALSE;

 complete behaviors;
 disjoint behaviors;
*/
static secure_bool_t regions_overlaps(const size_t a, const size_t b, size_t n)
{
    secure_bool_t res = SECURE_TRUE;

    if (a == b) {
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
  requires \valid(dest+(0..n-1));
  requires \valid_read(src+(0..n-1));
  requires separation: \separated(dest+(0..n-1),src+(0..n-1));
  assigns ((uint8_t*)dest)[0 .. (n-1)] \from indirect:src, indirect:n;
  assigns \result \from dest;
  ensures copied_contents: memcmp{Post,Pre}((char*)dest,(char*)src,n) == 0;
  ensures \forall integer i; 0 <= i < n ==> (dest[i] == src[i]);
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
  requires \separated((uint8_t*)src + (0 .. n-1), (uint8_t*)dest + (0 .. n-1));
  assigns ((uint8_t*)dest)[0 .. (n-1)] \from indirect:src, indirect:n;
  assigns \result \from indirect:src, indirect:n;
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
    if (unlikely(regions_overlaps((size_t)dest, (size_t)src, n) == SECURE_TRUE)) {
        goto err;
    }

    /*@ assert \separated((uint8_t*)dest + (0 .. n-1), (uint8_t*)src + (0 .. n-1)); */
    /*@ assert \valid((uint8_t*)dest + (0 .. (n-1))); */
    /*@ assert \valid_read((uint8_t*)dest + (0 .. (n-1))); */
    __sentry_memcpy(dest, src, n);
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
