/***************************************************************************//**
 * @file harness.c
 * @author Dorian Weber
 * @brief Source file containing the test-harness for tests.
 * 
 * This file will be linked instead of `main.c` for make-target `test`.
 ******************************************************************************/

#include <stdio.h>
#include "lexer_tests.h"

const int SEMANTIC_CHECK;

// auxiliary code for the test harness - only linked for target 'test'
int main(void) {
	#define X(CASE) do { \
		fputs(#CASE ": ", stderr); \
		fputs(CASE() ? "\033[32msuccess\033[0m\n" : "\n", stderr); \
	} while (0);
	
	LEXER_TESTS
	
	#undef X
	return 0;
}
