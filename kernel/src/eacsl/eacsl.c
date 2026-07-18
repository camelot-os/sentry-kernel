// SPDX-FileCopyrightText: 2025 H2Lab Development Team
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/panic.h>
#include <assert.h>
#include <mini-gmp.h>

/**
 * redefine runtime assert() to pro per kernel panic() call.
 * NOTE: there is no assert() direct call in the kernel code, but e-acsl generated
 * code do call it. The symbol is the
 */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wredundant-decls"
/** assert_func, called through assert() */
void __attribute__((noreturn)) 	__assert_func(
  const char *file __attribute__((unused)),
  int line __attribute__((unused)),
  const char *func __attribute__((unused)),
  const char *failedexpr __attribute__((unused)))
{
    panic(PANIC_UNEXPECTED_BRANCH_EXEC);
}

/** abort() definition */
void __attribute__((noreturn)) abort(void) {
  panic(PANIC_UNEXPECTED_BRANCH_EXEC);
}
#pragma GCC diagnostic pop



/* unused yet called in gmp lib */
void *realloc(void * ptr, size_t size) {
    assert(0);
}
#if 0
extern int __e_acsl_sound_verdict;

void __e_acsl_assert(int predicate, __e_acsl_assert_data_t * data) {
  printf("%s in file %s at line %d in function %s is %s (%s).\n\
The verified predicate was: `%s'.\n",
    data->kind,
    data->file,
    data->line,
    data->fct,
    predicate ? "valid" : "invalid",
    __e_acsl_sound_verdict ? "trustworthy" : "UNTRUSTWORTHY",
    data->pred_txt);
  if (data->values) {
    printf("With values:\n");
    __e_acsl_assert_data_value_t * value = data->values;
    while (value != NULL) {
      __e_acsl_print_value(value);
      value = value->next;
    }
  }
}


__e_acsl_assert_clean
__e_acsl_assert_copy_values
__e_acsl_assert_register_char
__e_acsl_assert_register_int
__e_acsl_assert_register_ptr
__e_acsl_assert_register_uint
__e_acsl_assert_register_ulong
__e_acsl_contract_get_behavior_assumes
__e_acsl_contract_partial_count_all_behaviors
__e_acsl_contract_set_behavior_assumes
__e_acsl_initialized
__e_acsl_offset
__e_acsl_separated
__e_acsl_valid
__e_acsl_valid_read
#endif
