%option noyywrap nounput noinput nodefault
%option never-interactive yylineno

WHITESPACE [[:space:]]
INTEGER    [[:digit:]]+
FLOAT      {INTEGER}"."{INTEGER}|"."{INTEGER}

%x COMMENT

%{
	#include <stdlib.h>
	#include "parser.tab.h"
%}

%%

{WHITESPACE}+ { /* ignore whitespaces */ }
"//".*\n      { /* ignore line comment */ }
"/*"          { BEGIN(COMMENT); }
<COMMENT>{
	"*/"      { BEGIN(INITIAL); }
	"*"[^/]   |
	[^*]+     |
	.         { /* ignore */ }
	<<EOF>>   { return YYUNDEF; }
}

"&&"          return LOG_AND;
"||"          return LOG_OR;
"=="          return EQ;
"!="          return NEQ;
"<="          return LEQ;
">="          return GEQ;
"<"           return LT;
">"           return GT;
"+"           return ADD;
"-"           return SUB;
"*"           return MUL;
"/"           return DIV;
"="           return ASSIGN;

"bool"        return KW_BOOLEAN;
"do"          return KW_DO;
"else"        return KW_ELSE;
"float"       return KW_FLOAT;
"for"         return KW_FOR;
"if"          return KW_IF;
"int"         return KW_INT;
"print"       return KW_PRINT;
"return"      return KW_RETURN;
"void"        return KW_VOID;
"while"       return KW_WHILE;

{FLOAT}([eE][\-+]?{INTEGER})? |
{INTEGER}([eE][\-+]?{INTEGER}) {
	yylval.floatValue = strtod(yytext, NULL);
	return FLOAT_LITERAL;
}
{INTEGER} {
	yylval.intValue = strtol(yytext, NULL, 10);
	return INT_LITERAL;
}
"true"      { yylval.intValue = 1; return BOOL_LITERAL; }
"false"     { yylval.intValue = 0; return BOOL_LITERAL; }
[[:alpha:]_][[:alnum:]_]* {
	yylval.string = malloc(yyleng + 1);
	strcpy(yylval.string, yytext);
	return IDENT;
}
\"[^\n\"]*\" {
	yylval.string = malloc(yyleng - 2 + 1);
	memcpy(yylval.string, yytext + 1, yyleng - 2);
	yylval.string[yyleng - 2] = 0;
	return STRING_LITERAL;
}

[;,(){}]      return *yytext;
.             return YYUNDEF;
<<EOF>>       return EOF;

%%

/* function needed during testing, please do not remove */
void lexer_reset_state(void) {
	BEGIN(INITIAL);
}
