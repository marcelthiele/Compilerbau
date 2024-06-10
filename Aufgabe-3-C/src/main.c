#include <stdio.h>
#include <stdlib.h>

#include <parser.tab.h>
#include <ast.h>

int SEMANTIC_CHECK = 0;

int main(int argc, const char *argv[]) {
	if (argc < 2) {
		fprintf(stderr, "Usage: %s <c1-source>\n", argv[0]);
		return EXIT_FAILURE;
	}
	
	// Open the source file.
	FILE *in = fopen(argv[1], "r");
	if (in == NULL) {
		fprintf(stderr, "Failed to read c1 source file\n");
		return EXIT_FAILURE;
	}
	
	// Parse it and print the syntax tree or report an error.
	yydebug = 1;
	ParseResult result = astParse(in);
	switch (result.tag) {
	case PARSE_OK:
		if (yydebug == 0)
			astProgramPrint(&result.ok, 0, stdout);
		astProgramRelease(&result.ok);
		break;
		
	default:
		fprintf(stdout, "%s\n", result.err);
		break;
	}
	
	return result.tag;
}
