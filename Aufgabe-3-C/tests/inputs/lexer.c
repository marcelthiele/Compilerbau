#include <stdio.h>
#include <stdlib.h>
#include <parser.tab.h>

YYSTYPE yylval;

const int SEMANTIC_CHECK;

int main(int argc, const char *argv[]) {
	int token;

	if (argc < 2) {
		fprintf(stderr, "Usage: %s <c1-source>\n", argv[0]);
		return EXIT_FAILURE;
	}

	// Open the source file.
	yyin = fopen(argv[1], "r");
	if (yyin == NULL) {
		fprintf(stderr, "Failed to read c1 source file\n");
		return EXIT_FAILURE;
	}

	// Run the lexer.
	while ((token = yylex()) != EOF) {
		const char *name;
		printf("Line: %3d, ", yylineno);
		switch (token) {
		case LOG_AND:
			name = "&&";
			break;
		case LOG_OR:
			name = "||";
			break;
		case EQ:
			name = "==";
			break;
		case NEQ:
			name = "!=";
			break;
		case LT:
			name = "<";
			break;
		case GT:
			name = ">";
			break;
		case LEQ:
			name = "<=";
			break;
		case GEQ:
			name = ">=";
			break;
		case ADD:
			name = "+";
			break;
		case SUB:
			name = "-";
			break;
		case MUL:
			name = "*";
			break;
		case DIV:
			name = "/";
			break;
		case ASSIGN:
			name = "=";
			break;
		case KW_BOOLEAN:
			name = "bool";
			break;
		case KW_DO:
			name = "do";
			break;
		case KW_ELSE:
			name = "else";
			break;
		case KW_FLOAT:
			name = "float";
			break;
		case KW_FOR:
			name = "for";
			break;
		case KW_IF:
			name = "if";
			break;
		case KW_INT:
			name = "int";
			break;
		case KW_PRINT:
			name = "print";
			break;
		case KW_RETURN:
			name = "return";
			break;
		case KW_VOID:
			name = "void";
			break;
		case KW_WHILE:
			name = "while";
			break;

		case IDENT:
			printf("IDENT:  <%s>\n", yylval.string);
			continue;

		case BOOL_LITERAL:
			printf("BOOL:   <%s>\n", yylval.intValue ? "true" : "false");
			continue;

		case INT_LITERAL:
			printf("INT:    <%d>\n", yylval.intValue);
			continue;

		case FLOAT_LITERAL:
			printf("FLOAT:  <%g>\n", yylval.floatValue);
			continue;

		case STRING_LITERAL:
			printf("STRING: <%s>\n", yylval.string);
			continue;
			
		case YYUNDEF:
			printf("Token:  INVALID\n");
			return EXIT_SUCCESS;
		}

		if (token <= 255)
			printf("Token:  '%c'\n", token);
		else
			printf("Token:  \"%s\"\n", name);
	}

	return EXIT_SUCCESS;
}
