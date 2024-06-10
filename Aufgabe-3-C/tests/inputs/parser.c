#include <stdio.h>
#include <stdlib.h>

#include <ast.h>
#include <parser.tab.h>

const int SEMANTIC_CHECK = 0;

int main(int argc, const char *argv[]) {
	if (argc < 2) {
		fprintf(stderr, "Usage: %s <c1-source>\n", argv[0]);
		return EXIT_FAILURE;
	}
	
	FILE *in = fopen(argv[1], "r");
	if (in == NULL) {
		fprintf(stderr, "Failed to read c1 source file\n");
		return EXIT_FAILURE;
	}
	
	ParseResult result = astParse(in);
	switch (result.tag) {
	case PARSE_OK:
		astProgramPrint(&result.ok, 0, stdout);
		astProgramRelease(&result.ok);
		break;
		
	default:
		puts(result.err);
		break;
	}
	
	return result.tag;
}
