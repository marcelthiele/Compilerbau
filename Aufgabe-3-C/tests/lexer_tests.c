#include "lexer_tests.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <parser.tab.h>

// import some flex functions for parsing from memory
typedef struct yy_buffer_state* YY_BUFFER_STATE;
extern YY_BUFFER_STATE yy_scan_string(const char *base);
extern void yy_delete_buffer(YY_BUFFER_STATE b);
extern void lexer_reset_state(void);

YYSTYPE yylval;

typedef struct {
	const char *input;
	int token;
	YYSTYPE value;
} Expectation[];

/**
 * @brief Helper macro to compare and diagnose differences between expected and
 * actual output.
 * @param LHS    the left-hand-side of the comparison
 * @param RHS    the right-hand-side of the comparison
 * @param FMT    a format-specifier to print \p LHS and \p RHS
 * @param INPUT  the input string for diagnostic purposes
 */
#define EXPECT_EQ(LHS, RHS, FMT, INPUT) \
	if (LHS != RHS) { \
		fprintf(stderr, "assertion `" #LHS " == " #RHS "` failed [%s]", INPUT); \
		fprintf(stderr, "\n\tleft: " FMT ",\n\tright: " FMT, LHS, RHS); \
		return false; \
	}

static int scan(const char *input) {
	YY_BUFFER_STATE buf = yy_scan_string(input);
	int result = yylex();
	lexer_reset_state();
	yy_delete_buffer(buf);
	return result;
}

bool lexer_empty_stream(void) {
	EXPECT_EQ(scan(""), EOF, "%i", "");
	return true;
}

bool lexer_bool_literals(void) {
	Expectation io = {
		{ "true", BOOL_LITERAL, { .intValue = 1 } },
		{ "false", BOOL_LITERAL, { .intValue = 0 } },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), BOOL_LITERAL, "%i", io[i].input);
		EXPECT_EQ(yylval.intValue, io[i].value.intValue, "%i", io[i].input);
	}
	
	return true;
}

bool lexer_float_literals(void) {
	Expectation io = {
		{ "1.0", FLOAT_LITERAL, { .floatValue = 1.0 } },
		{ ".01", FLOAT_LITERAL, { .floatValue = .01 } },
		{ "3.1e-12", FLOAT_LITERAL, { .floatValue = 3.1e-12 } },
		{ "2E3", FLOAT_LITERAL, { .floatValue = 2E3 } },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), io[i].token, "%i", io[i].input);
		EXPECT_EQ(yylval.floatValue, io[i].value.floatValue, "%f", io[i].input);
	}
	
	return true;
}

bool lexer_int_literals(void) {
	Expectation io = {
		{ "13", INT_LITERAL, { .intValue = 13 } },
		{ "001", INT_LITERAL, { .intValue = 1 } },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), INT_LITERAL, "%i", io[i].input);
		EXPECT_EQ(yylval.intValue, io[i].value.intValue, "%i", io[i].input);
	}
	
	return true;
}

bool lexer_string_literals(void) {
	Expectation io = {
		{ "\"\"", STRING_LITERAL, { .string = "" } },
		{ "\"Hallo\"", STRING_LITERAL, { .string = "Hallo" } },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), STRING_LITERAL, "%i", io[i].input);
		
		if (strcmp(yylval.string, io[i].value.string) != 0) {
			fprintf(stderr, "assertion `yylval.string == io[i].value.string` failed [%s]", io[i].input);
			fprintf(stderr, "\n\tleft: \"%s\",\n\tright: \"%s\"", yylval.string, io[i].value.string);
			return false;
		}
	}
	
	return true;
}

bool lexer_identifiers(void) {
	Expectation io = {
		{ "Lexer", IDENT, { .string = "Lexer" } },
		{ "is_power_of_two", IDENT, { .string = "is_power_of_two" } },
		{ "LOG_2", IDENT, { .string = "LOG_2" } },
		{ "_underscore", IDENT, { .string = "_underscore" } },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), IDENT, "%i", io[i].input);
		
		if (strcmp(yylval.string, io[i].value.string) != 0) {
			fprintf(stderr, "assertion `yylval.string == io[i].value.string` failed [%s]", io[i].input);
			fprintf(stderr, "\n\tleft: \"%s\",\n\tright: \"%s\"", yylval.string, io[i].value.string);
			return false;
		}
	}
	
	return true;
}

bool lexer_keywords(void) {
	Expectation io = {
		{ "bool", KW_BOOLEAN },
		{ "do", KW_DO },
		{ "else", KW_ELSE },
		{ "for", KW_FOR },
		{ "float", KW_FLOAT },
		{ "if", KW_IF },
		{ "int", KW_INT },
		{ "print", KW_PRINT },
		{ "return", KW_RETURN },
		{ "void", KW_VOID },
		{ "while", KW_WHILE },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), io[i].token, "%i", io[i].input);
	}
	
	return true;
}

bool lexer_operators(void) {
	Expectation io = {
		{ "+", ADD },
		{ "-", SUB },
		{ "*", MUL },
		{ "/", DIV },
		{ "=", ASSIGN },
		{ "==", EQ },
		{ "!=", NEQ },
		{ "<", LT },
		{ ">", GT },
		{ "<=", LEQ },
		{ ">=", GEQ },
		{ "&&", LOG_AND },
		{ "||", LOG_OR },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), io[i].token, "%i", io[i].input);
	}
	
	return true;
}

bool lexer_separators(void) {
	Expectation io = {
		{ ";", ';' },
		{ ",", ',' },
		{ "(", '(' },
		{ ")", ')' },
		{ "{", '{' },
		{ "}", '}' },
	};
	
	for (int i = 0; i < sizeof(io)/sizeof(*io); ++i) {
		EXPECT_EQ(scan(io[i].input), io[i].token, "%i", io[i].input);
	}
	
	return true;
}

bool lexer_unclosed_c_comment(void) {
	EXPECT_EQ(scan("/*"), YYUNDEF, "%i", "/*");
	return true;
}

bool lexer_illegal_character(void) {
	YY_BUFFER_STATE buf = yy_scan_string("100%");
	EXPECT_EQ(yylex(), INT_LITERAL, "%i", "100");
	EXPECT_EQ(yylex(), YYUNDEF, "%i", "%");
	lexer_reset_state();
	yy_delete_buffer(buf);
	
	return true;
}
