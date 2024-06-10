%define parse.error verbose
%define parse.trace
%parse-param {ParseResult *result}

%code requires {
	#include <stdio.h>
	#include <stdarg.h>
	#include "ast.h"
	#include "vec.h"
	
	typedef struct ParseResult ParseResult;
	
	extern int yylex(void);
	extern int yylineno;
	extern FILE *yyin;
}

%code provides {
	/**
	 * Variantentyp des Ergebnisses des Parsevorganges.
	 */
	struct ParseResult {
		enum ParseResultTag {
			PARSE_OK,
			PARSE_ERR_SYNTAX
		} tag;
		
		union {
			Program ok;
			char err[256];
		};
	};
	
	/**
	 * Die obere Parse-Funktion: wandelt den Eingabestrom in einen AST (`Program`)
	 * um oder gibt eine Fehlermeldung zurück, falls das Programm inkorrekt ist.
	 */
	extern ParseResult astParse(FILE *input);
	
	/**
	 * @brief Speichert die Fehlermeldung für den Rufer.
	 * Die Funktion akzeptiert eine variable Argumentliste und nutzt die Syntax von
	 * printf.
	 * @param result  Zeiger auf das Ausgabeargument der parse-Funktion
	 * @param msg     die Fehlermeldung
	 * @param ...     variable Argumentliste für die Formatierung von \p msg
	 */
	extern void yyerror(ParseResult *result, const char *msg, ...);
}

%union {
	/* lexical token types */
	char *string;
	double floatValue;
	int intValue;
	
	/* ast types */
	Item item;
	
	FuncDef func_def;
	FuncParam func_param;
	FuncCall func_call;
	
	Block block;
	
	Stmt stmt;
	IfStmt if_stmt;
	ForStmt for_stmt;
	WhileStmt while_stmt;
	PrintStmt print_stmt;
	VarDef var_def;
	
	Assign assign;
	Expr expr;
	
	DataType type;
	
	/* vectors of ast types */
	FuncParam *func_params;
	Stmt *stmts;
	Expr *exprs;
}

/* define the printer routines for improved debug output */
%printer { fprintf(yyoutput, "\"%s\"", $$); }     <string>
%printer { fprintf(yyoutput, "%g", $$); }         <floatValue>
%printer { fprintf(yyoutput, "%i", $$); }         <intValue>
%printer { astItemPrint(&$$, 0, yyoutput); }      <item>
%printer { astFuncDefPrint(&$$, 0, yyoutput); }   <func_def>
%printer { astFuncParamPrint(&$$, 0, yyoutput); } <func_param>
%printer { astFuncCallPrint(&$$, 0, yyoutput); }  <func_call>
%printer { astBlockPrint(&$$, 0, yyoutput); }     <block>
%printer { astStmtPrint(&$$, 0, yyoutput); }      <stmt>
%printer { astIfStmtPrint(&$$, 0, yyoutput); }    <if_stmt>
%printer { astForStmtPrint(&$$, 0, yyoutput); }   <for_stmt>
%printer { astWhileStmtPrint(&$$, 0, yyoutput); } <while_stmt>
%printer { astPrintStmtPrint(&$$, 0, yyoutput); } <print_stmt>
%printer { astVarDefPrint(&$$, 0, yyoutput); }    <var_def>
%printer { astAssignPrint(&$$, 0, yyoutput); }    <assign>
%printer { astExprPrint(&$$, 0, yyoutput); }      <expr>

/* define destructors in order to prevent memory leaks */
%destructor { free($$); }                 <string>
%destructor { astItemRelease(&$$); }      <item>
%destructor { astFuncDefRelease(&$$); }   <func_def>
%destructor { astFuncParamRelease(&$$); } <func_param>
%destructor { astFuncCallRelease(&$$); }  <func_call>
%destructor { astBlockRelease(&$$); }     <block>
%destructor { astStmtRelease(&$$); }      <stmt>
%destructor { astIfStmtRelease(&$$); }    <if_stmt>
%destructor { astForStmtRelease(&$$); }   <for_stmt>
%destructor { astWhileStmtRelease(&$$); } <while_stmt>
%destructor { astPrintStmtRelease(&$$); } <print_stmt>
%destructor { astVarDefRelease(&$$); }    <var_def>
%destructor { astAssignRelease(&$$); }    <assign>
%destructor { astExprRelease(&$$); }      <expr>

%destructor {
	if ($$ != NULL) {
		vecForEach(FuncParam *e, $$) {
			astFuncParamRelease(e);
		}
		vecRelease($$);
	}
} <func_params>

%destructor {
	if ($$ != NULL) {
		vecForEach(Stmt *e, $$) {
			astStmtRelease(e);
		}
		vecRelease($$);
	}
} <stmts>

%destructor {
	if ($$ != NULL) {
		vecForEach(Expr *e, $$) {
			astExprRelease(e);
		}
		vecRelease($$);
	}
} <exprs>

/* extra token declaration to support versions of bison older than 3.6;
 * ignore the warning in your editor */
%token YYUNDEF

/* used tokens (KW is abbreviation for keyword) */
%token LOG_AND      "&&"
%token LOG_OR       "||"
%token EQ           "=="
%token NEQ          "!="
%token LT           "<"
%token GT           ">"
%token LEQ          "<="
%token GEQ          ">="
%token ADD          "+"
%token SUB          "-"
%token MUL          "*"
%token DIV          "/"
%token ASSIGN       "="
%token KW_BOOLEAN   "bool"
%token KW_DO        "do"
%token KW_ELSE      "else"
%token KW_FLOAT     "float"
%token KW_FOR       "for"
%token KW_IF        "if"
%token KW_INT       "int"
%token KW_PRINT     "print"
%token KW_RETURN    "return"
%token KW_VOID      "void"
%token KW_WHILE     "while"
%token <intValue>   INT_LITERAL
%token <floatValue> FLOAT_LITERAL
%token <intValue>   BOOL_LITERAL
%token <string>     STRING_LITERAL
%token <string>     IDENT

%%

program:
	/* empty */
	;

%%

void yyerror(ParseResult *result, const char* msg, ...) {
	va_list args;
	int len = 0;
	
	/* free the space for the ok-branch and set the error code */
	if (result->tag == PARSE_OK) {
		astProgramRelease(&result->ok);
	}
	
	result->tag = PARSE_ERR_SYNTAX;
	
	/* print the message into the buffer */
	va_start(args, msg);
	len = snprintf(result->err, sizeof(result->err), "Error in line %d: ", yylineno);
	vsnprintf(result->err + len, sizeof(result->err) - len, msg, args);
	va_end(args);
}

ParseResult astParse(FILE *input) {
	ParseResult result = {
		.tag = PARSE_OK,
		.ok = astProgramNew()
	};
	yyin = input;
	yyparse(&result);
	return result;
}
