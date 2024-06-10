#ifndef LEXER_TESTS_H_INCLUDED
#define LEXER_TESTS_H_INCLUDED

#include <stdbool.h>

/**
 * [X-Macro](https://en.wikipedia.org/wiki/X_macro) containing the names
 * of the test cases.
 */
#define LEXER_TESTS \
	X(lexer_empty_stream) \
	X(lexer_bool_literals) \
	X(lexer_float_literals) \
	X(lexer_int_literals) \
	X(lexer_string_literals) \
	X(lexer_identifiers) \
	X(lexer_keywords) \
	X(lexer_operators) \
	X(lexer_separators) \
	X(lexer_unclosed_c_comment) \
	X(lexer_illegal_character)

/* declare the test functions based on the list */
#define X(CASE) extern bool CASE(void);
LEXER_TESTS
#undef X

#endif
