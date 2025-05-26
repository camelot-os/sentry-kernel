// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <sentry/ktypes.h>

/* string related functions, for debug usage only */
/*@
  requires s != \null ==> \valid_read(s + (0 .. maxlen - 1));

  assigns \nothing;

  behavior null_pointer:
    assumes s == \null;
    ensures \result == 0; // If s is null, the length is 0
  behavior valid_string:
   assumes s != \null;
   ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';
   ensures \result < maxlen ==> s[\result] == '\0';
   ensures \result == maxlen ==> \forall integer i; 0 <= i < maxlen ==> s[i] != '\0';

  complete behaviors;
  disjoint behaviors;
  */
#ifndef __FRAMAC__
static
#endif
size_t sentry_strnlen(const char *s, size_t maxlen)
{
    size_t result = 0;

    if (s == NULL) {
        /** TODO: panic to be called */
        goto err;
    }
    /*@
      @ loop invariant 0 <= result <= maxlen;
      @ loop invariant \forall integer i; 0 <= i < result ==> s[i] != '\0';
      @ loop assigns result, s[0 .. (maxlen - 1)];
      @ loop variant maxlen - result;
      */
    while ((s[result] != '\0') && result < maxlen) {
        result++;
    }
err:
    return result;
}

/**
 * @brief Set n first bytes of a given memory area with a given byte value
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
/*@
  requires s != \null ==> \valid((uint8_t*)s + (0 .. n - 1));

  behavior null_pointer:
    assumes s == \null;
    assigns \nothing;
    ensures \result == s; // If s is null, return it unchanged
  behavior valid_string:
   assumes s != \null;
   ensures \forall integer i; 0 <= i < n ==> ((uint8_t*)s)[i] == c;
   ensures \result == s;

  complete behaviors;
  disjoint behaviors;
  */
#ifndef __FRAMAC__
static
#endif
void   *sentry_memset(void *s, int c, unsigned int n)
{
    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (unlikely(!s)) {
        goto err;
    }

    /* memseting s with c */
    char   *bytes = s;
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall integer k; 0 <= k < i ==> bytes[k] == c;
      @ loop assigns i, bytes[0 .. (n-1)];
      @ loop variant n - i;
      */
    for (unsigned int i = 0; i < n; i++) {
        *bytes = c;
        bytes++;
    }
err:
    return s;
}

/**
 *  auxiliary function that returns SECURE_FALSE if regions
 *  a[0..n-1] and b[0..n-1] do not overlap, or SECURE_TRUE otherwise
 */
/*@
 assigns \result \from indirect:a, indirect:b, indirect:n;

 behavior separated:
  assumes separation:no_overlap: \separated((uint8_t*)a + (0 .. n-1), (uint8_t*)b + (0 .. n-1));
  ensures result_no_overlap: \result == SECURE_FALSE;
 behavior not_separated_lt:
  assumes separation:overlap: !\separated((uint8_t*)a + (0 .. n-1), (uint8_t*)b + (0 .. n-1));
  assumes a_before_b:  (uint8_t*)a <= (uint8_t*)b < (uint8_t*)a + n;
  ensures result_a_before_b: \result == SECURE_TRUE;
 behavior not_separated_gt:
  assumes separation:overlap: !\separated((uint8_t*)a + (0 .. n-1), (uint8_t*)b + (0 .. n-1));
  assumes a_after_b: (uint8_t*)b <  (uint8_t*)a <= (uint8_t*)b + n;
  ensures result_a_after_b: \result == SECURE_TRUE;

 complete behaviors;
 disjoint behaviors;
*/
static secure_bool_t regions_overlaps(const void* a, const void* b, unsigned int n)
{
    secure_bool_t res = SECURE_TRUE;
    size_t _a = (size_t)a;
    size_t _b = (size_t)b;
    if ((_a < _b) && ((_a + n) > _b)) {
        goto err;
    }
    if ((_a > _b) && ((_b + n) > _a)) {
        goto err;
    }
    res = SECURE_FALSE;
err:
    return res;
}

/*@
  // initial implications:
  requires dest != \null ==> \valid((uint8_t*)dest + (0 .. n-1));
  requires src != \null ==> \valid_read((uint8_t*)src + (0 .. n-1));
    behavior null_pointer:
    assumes dest == \null || src == \null;
    assigns \nothing;
    ensures \result == dest;
  behavior overlap:
    assumes dest != \null && src != \null;
    assumes !\separated((uint8_t*)dest + (0 .. n-1), (uint8_t*)src + (0 .. n-1));
    assigns \nothing;
    ensures \result == dest;
  behavior copy:
    assumes dest != \null && src != \null;
    assumes \separated((uint8_t*)dest + (0 .. n-1), (uint8_t*)src + (0 .. n-1));
    assigns ((uint8_t*)dest)[0 .. n-1];
    ensures \forall integer i; 0 <= i < n ==> ((uint8_t*)dest)[i] == ((uint8_t*)src)[i];
    ensures \result == dest;
  complete behaviors;
  disjoint behaviors;
  */
#ifndef __FRAMAC__
static
#endif
void   *sentry_memcpy(void * restrict dest, const void* restrict src, size_t n)
{
    if (unlikely(!dest || !src)) {
        goto err;
    }
    if (unlikely(regions_overlaps(dest, src, n) == SECURE_TRUE)) {
        goto err;
    }

    uint32_t *s = (uint32_t*)src;
    uint32_t *d = (uint32_t*)dest;

    /* copy word by word */
    /*@
      @ loop invariant 0 <= i <= (n / 4);
      @ loop invariant \forall ℤ k; 0 <= k < i ==> d[k] == s[k];
      @ loop assigns i, d[0 .. ((n / 4) - 1)];
      @ loop variant n - i;
      */
    for (size_t i = 0; i < n / 4; i++) {
        *d = *s;
        d++;
        s++;
    }
    /* if n is not word aligned, finishing with last bytes */
    uint8_t *s8 = (uint8_t*)s;
    uint8_t *d8 = (uint8_t*)d;

    /*@
      @ loop invariant 0 <= i <= (n % 4);
      @ loop invariant \forall ℤ k; 0 <= k < i ==> d8[k] == s8[k];
      @ loop assigns i, d8[0 .. (n-1)];
      @ loop variant n - i;
      */
    for (size_t i = 0; i < n % 4; i++) {
        *d8 = *s8;
        d8++;
        s8++;
    }
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
