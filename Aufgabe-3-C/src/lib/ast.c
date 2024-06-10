/***************************************************************************//**
 * @file ast.c
 * Implementation des Syntaxbaumes.
 ******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "parser.tab.h"
#include "ast.h"
#include "vec.h"

/* *** internal helpers **************************************************** */

/**
 * Makro zur vereinfachten Implementation von Debug-Print Routinen für
 * Struktur-Typen.
 */
#define STRUCT(TYPE, ...) do {            \
	const char *sep = "";                 \
	fputs("(" #TYPE ") {", out);          \
	indent++;                             \
	__VA_ARGS__;                          \
	indent--;                             \
	fprintf(out, "\n%*s}", indent*4, ""); \
} while (0)

/**
 * Makro zur Debug-Print Ausgabe von Varianten eines Variantentyps.
 */
#define CHOICE(NAME, ...) do { \
	fputs(#NAME "(", out);     \
	__VA_ARGS__;               \
	fputs(")", out);           \
} while (0)

/**
 * Makro zur Ausgabe von Strukturfeldern mit Strukturtyp.
 */
#define FIELD(NAME, ...) do {                                \
	fprintf(out, "%s\n%*s." #NAME " = ", sep, indent*4, ""); \
	__VA_ARGS__;                                             \
	sep = ",";                                               \
} while (0)

/**
 * Makro zur Ausgabe von Strukturfeldern mit Vektortyp.
 */
#define VEC_FIELD(NAME, ...) do {                             \
	fprintf(out, "%s\n%*s." #NAME " = [", sep, indent*4, ""); \
	if (vecLen(self->NAME) == 0) {                            \
		fputs("]", out); break;                               \
	}                                                         \
	sep = "";                                                 \
	indent++;                                                 \
	for (unsigned int i = 0; i < vecLen(self->NAME); ++i) {   \
		fprintf(out, "%s\n%*s[%u] = ", sep, indent*4, "", i); \
		sep = ",";                                            \
		__VA_ARGS__;                                          \
	}                                                         \
	indent--;                                                 \
	sep = ",";                                                \
	fprintf(out, "\n%*s]", indent*4, "");                     \
} while (0)

/**
 * Makro zur Ausgabe von Strukturfeldern mit Zeigertyp.
 */
#define STR_FIELD(NAME) do { \
	fprintf(out, "%s\n%*s." #NAME " = \"%s\"", sep, indent*4, "", self->NAME); \
	sep = ",";                                                                 \
} while (0)

/**
 * Makro zur Ausgabe von Strukturfeldern mit Integertyp.
 */
#define INT_FIELD(NAME) do { \
	fprintf(out, "%s\n%*s." #NAME " = %i", sep, indent*4, "", self->NAME); \
	sep = ",";                                                             \
} while (0)

const char *TYPE_NAMES[] = {
	[TYPE_VOID]  = "void",
	[TYPE_BOOL]  = "bool",
	[TYPE_INT]   = "int",
	[TYPE_FLOAT] = "float"
};

const char *BIN_OP_NAMES[] = {
	[BIN_OP_ADD] = "Add",
	[BIN_OP_SUB] = "Sub",
	[BIN_OP_MUL] = "Mul",
	[BIN_OP_DIV] = "Div",
	[BIN_OP_LOG_OR] = "LogOr",
	[BIN_OP_LOG_AND] = "LogAnd",
	[BIN_OP_EQ] = "Eq",
	[BIN_OP_NEQ] = "Neq",
	[BIN_OP_LT] = "Lt",
	[BIN_OP_GT] = "Gt",
	[BIN_OP_LEQ] = "Leq",
	[BIN_OP_GEQ] = "Geq"
};

/**
 * Hilfsfunktion zur Allocation von Heap-Speicher und Kopie einer
 * Variablen.
 **/
static void* BOX(void *ptr, size_t size) {
	void *result = malloc(size);
	
	if (result == NULL) {
		fputs("out-of-memory error\n", stderr);
		exit(-1);
	}
	
	memcpy(result, ptr, size);
	return result;
}

/**
 * Bewegt eine Stackvariable auf den Heap und gibt einen Zeiger darauf
 * zurück.
 **/
#define BOX(instance) \
	BOX(&instance, sizeof(instance))

/* Eine externe Variable, die das Hauptprogramm setzt, um die Debug-Ausgabe
 * zu beeinflussen. Für den Wert 0 werden keine semantischen Informationen
 * wie das res-Feld in ResIdent oder das data_type-Feld in Expr ausgegeben,
 * für Werte ungleich 0 werden sie ausgegeben.
 * 
 * Das ist notwendig, damit der Referenzinterpreter weiterhin diff-bare
 * Ausgaben für den abstrakten Syntaxbaum ausgeben kann. */
extern const int SEMANTIC_CHECK;

const DefId INVALID_DEF_ID = { -1u };

const ItemId INVALID_ITEM_ID = { -1u };

/* *** implementation ****************************************************** */

/* *** constructor functions */

Program astProgramNew(void) {
	Program result;
	vecInit(result.items);
	return result;
}

Item astItemFromVarDef(VarDef var_def) {
	return (Item) {
		.tag = ITEM_GLOBAL_VAR,
		.var_def = var_def
	};
}

Item astItemFromFuncDef(FuncDef func_def) {
	return (Item) {
		.tag = ITEM_FUNC,
		.func_def = func_def
	};
}

FuncDef astFuncDefNew(DataType return_type, char *ident, FuncParam *params, Stmt *statements) {
	if (params == NULL) { vecInit(params); }
	if (statements == NULL) { vecInit(statements); }
	
	return (FuncDef) {
		.return_type = return_type,
		.ident = ident,
		.params = params,
		.statements = statements
	};
}

FuncCall astFuncCallNew(char *ident, Expr *args) {
	if (args == NULL) { vecInit(args); }
	
	return (FuncCall) {
		.res_ident = { .ident = ident, .res = INVALID_DEF_ID },
		.args = args
	};
}

FuncParam astFuncParamNew(DataType data_type, char *ident) {
	return (FuncParam) {
		.data_type = data_type,
		.ident = ident
	};
}

Expr astExprFromAssign(Assign assign) {
	return (Expr) {
		.tag = EXPR_ASSIGN,
		.assign = assign
	};
}

Expr astExprFromFuncCall(FuncCall func_call) {
	return (Expr) {
		.tag = EXPR_CALL,
		.call = func_call
	};
}

Expr astExprFromIdent(char *ident) {
	return (Expr) {
		.tag = EXPR_VAR,
		.var = { .ident = ident, .res = INVALID_DEF_ID }
	};
}

Expr astExprFromLiteral(Literal literal) {
	return (Expr) {
		.tag = EXPR_LITERAL,
		.literal = literal
	};
}

Expr astExprFromUnaryMinus(Expr expr) {
	return (Expr) {
		.tag = EXPR_UNARY_MINUS,
		.unary_minus = BOX(expr)
	};
}

Expr astExprFromBinOpExpr(Expr lhs, Expr rhs, BinOp op) {
	return (Expr) {
		.tag = EXPR_BIN_OP,
		.bin_op = {
			.op = op,
			.lhs = BOX(lhs),
			.rhs = BOX(rhs)
		}
	};
}

Literal astLiteralFromInt(int value) {
	return (Literal) {
		.tag = LITERAL_INT,
		.iVal = value
	};
}

Literal astLiteralFromFloat(double value) {
	return (Literal) {
		.tag = LITERAL_FLOAT,
		.fVal = value
	};
}

Literal astLiteralFromBool(int value) {
	return (Literal) {
		.tag = LITERAL_BOOL,
		.bVal = value
	};
}

Assign astAssignNew(char *lhs, Expr rhs) {
	return (Assign) {
		.lhs = { .ident = lhs, .res = INVALID_DEF_ID },
		.rhs = BOX(rhs)
	};
}

Stmt astStmtNew(void) {
	return (Stmt) { .tag = STMT_EMPTY };
}

Stmt astStmtFromIfStmt(IfStmt if_stmt) {
	return (Stmt) {
		.tag = STMT_IF,
		.if_stmt = if_stmt
	};
}

Stmt astStmtFromForStmt(ForStmt for_stmt) {
	return (Stmt) {
		.tag = STMT_FOR,
		.for_stmt = for_stmt
	};
}

Stmt astStmtFromWhileStmt(WhileStmt stmt) {
	return (Stmt) {
		.tag = STMT_WHILE,
		.while_stmt = stmt
	};
}

Stmt astStmtFromDoWhileStmt(WhileStmt stmt) {
	return (Stmt) {
		.tag = STMT_DO_WHILE,
		.do_while_stmt = stmt
	};
}

Stmt astStmtFromReturn(Expr *return_val) {
	return (Stmt) {
		.tag = STMT_RETURN,
		.return_stmt = return_val == NULL ? (Expr) {
			.tag = EXPR_INVALID
		} : *return_val
	};
}

Stmt astStmtFromPrintStmt(PrintStmt print_stmt) {
	return (Stmt) {
		.tag = STMT_PRINT,
		.print_stmt = print_stmt
	};
}

Stmt astStmtFromVarDef(VarDef var_def) {
	return (Stmt) {
		.tag = STMT_VAR_DEF,
		.var_def = var_def
	};
}

Stmt astStmtFromAssign(Assign assign) {
	return (Stmt) {
		.tag = STMT_ASSIGN,
		.assign = assign
	};
}

Stmt astStmtFromFuncCall(FuncCall call) {
	return (Stmt) {
		.tag = STMT_CALL,
		.call = call
	};
}

Stmt astStmtFromBlock(Block block) {
	return (Stmt) {
		.tag = STMT_BLOCK,
		.block = block
	};
}

IfStmt astIfStmtNew(Expr cond, Stmt if_true, Stmt if_false) {
	return (IfStmt) {
		.cond = cond,
		.if_true = BOX(if_true),
		.if_false = BOX(if_false)
	};
}

WhileStmt astWhileStmtNew(Expr cond, Stmt body) {
	return (WhileStmt) {
		.cond = cond,
		.body = BOX(body)
	};
}

ForStmt astForStmtNew(ForInit init, Expr cond, Assign update, Stmt body) {
	return (ForStmt) {
		.init = init,
		.cond = cond,
		.update = update,
		.body = BOX(body)
	};
}

ForInit astForInitFromVarDef(VarDef var_def) {
	return (ForInit) {
		.tag = FOR_INIT_VAR_DEF,
		.var_def = var_def
	};
}

ForInit astForInitFromAssign(Assign assign) {
	return (ForInit) {
		.tag = FOR_INIT_ASSIGN,
		.assign = assign
	};
}

PrintStmt astPrintStmtFromString(char *string) {
	return (PrintStmt) {
		.tag = PRINT_STRING,
		.string = string
	};
}

PrintStmt astPrintStmtFromExpr(Expr expr) {
	return (PrintStmt) {
		.tag = PRINT_EXPR,
		.expr = expr
	};
}

VarDef astVarDefNew(DataType data_type, char *ident, Expr *init) {
	return (VarDef) {
		.data_type = data_type,
		.res_ident = { .ident = ident, .res = INVALID_DEF_ID },
		.init = init == NULL ? (Expr) {
			.tag = EXPR_INVALID
		} : *init
	};
}

Block astBlockNew(Stmt *statements) {
	if (statements == NULL) { vecInit(statements); }
	
	return (Block) {
		.statements = statements
	};
}

/* *** destructor routines */

void astProgramRelease(Program *self) {
	vecForEach(Item *item, self->items) {
		astItemRelease(item);
	}
	
	vecRelease(self->items);
}

void astItemRelease(Item *self) {
	switch (self->tag) {
	case ITEM_GLOBAL_VAR:
		astVarDefRelease(&self->var_def);
		break;
		
	case ITEM_FUNC:
		astFuncDefRelease(&self->func_def);
		break;
	}
}

void astFuncDefRelease(FuncDef *self) {
	vecForEach(FuncParam *param, self->params) {
		astFuncParamRelease(param);
	}
	
	vecForEach(Stmt *stmt, self->statements) {
		astStmtRelease(stmt);
	}
	
	vecRelease(self->params);
	vecRelease(self->statements);
	free(self->ident);
}

void astFuncCallRelease(FuncCall *self) {
	vecForEach(Expr *arg, self->args) {
		astExprRelease(arg);
	}
	
	vecRelease(self->args);
	free(self->res_ident.ident);
}

void astFuncParamRelease(FuncParam *self) {
	free(self->ident);
}

void astExprRelease(Expr *self) {
	switch (self->tag) {
	case EXPR_INVALID:
		break;
		
	case EXPR_ASSIGN:
		astAssignRelease(&self->assign);
		break;
		
	case EXPR_BIN_OP:
		astExprRelease(self->bin_op.lhs);
		astExprRelease(self->bin_op.rhs);
		break;
		
	case EXPR_UNARY_MINUS:
		astExprRelease(self->unary_minus);
		break;
		
	case EXPR_CALL:
		astFuncCallRelease(&self->call);
		break;
		
	case EXPR_LITERAL:
		astLiteralRelease(&self->literal);
		break;
		
	case EXPR_VAR:
		free(self->var.ident);
		break;
	}
}

void astLiteralRelease(Literal *self) { /* empty */ }

void astAssignRelease(Assign *self) {
	free(self->lhs.ident);
	astExprRelease(self->rhs);
	free(self->rhs);
}

void astStmtRelease(Stmt *self) {
	switch (self->tag) {
	case STMT_EMPTY:
		break;
		
	case STMT_IF:
		astIfStmtRelease(&self->if_stmt);
		break;
		
	case STMT_FOR:
		astForStmtRelease(&self->for_stmt);
		break;
		
	case STMT_WHILE:
		astWhileStmtRelease(&self->while_stmt);
		break;
		
	case STMT_DO_WHILE:
		astWhileStmtRelease(&self->do_while_stmt);
		break;
		
	case STMT_RETURN:
		astExprRelease(&self->return_stmt);
		break;
		
	case STMT_PRINT:
		astPrintStmtRelease(&self->print_stmt);
		break;
		
	case STMT_VAR_DEF:
		astVarDefRelease(&self->var_def);
		break;
		
	case STMT_ASSIGN:
		astAssignRelease(&self->assign);
		break;
		
	case STMT_CALL:
		astFuncCallRelease(&self->call);
		break;
		
	case STMT_BLOCK:
		astBlockRelease(&self->block);
		break;
	}
}

void astIfStmtRelease(IfStmt *self) {
	astExprRelease(&self->cond);
	astStmtRelease(self->if_true);
	astStmtRelease(self->if_false);
	free(self->if_true);
	free(self->if_false);
}

void astWhileStmtRelease(WhileStmt *self) {
	astExprRelease(&self->cond);
	astStmtRelease(self->body);
	free(self->body);
}

void astForStmtRelease(ForStmt *self) {
	astForInitRelease(&self->init);
	astExprRelease(&self->cond);
	astAssignRelease(&self->update);
	astStmtRelease(self->body);
	free(self->body);
}

void astForInitRelease(ForInit *self) {
	switch (self->tag) {
	case FOR_INIT_VAR_DEF:
		astVarDefRelease(&self->var_def);
		break;
		
	case FOR_INIT_ASSIGN:
		astAssignRelease(&self->assign);
		break;
	}
}

void astPrintStmtRelease(PrintStmt *self) {
	switch (self->tag) {
	case PRINT_STRING:
		free(self->string);
		break;
		
	case PRINT_EXPR:
		astExprRelease(&self->expr);
		break;
	}
}

void astVarDefRelease(VarDef *self) {
	free(self->res_ident.ident);
	astExprRelease(&self->init);
}

void astBlockRelease(Block *self) {
	vecForEach(Stmt *stmt, self->statements) {
		astStmtRelease(stmt);
	}
	vecRelease(self->statements);
}

/* *** debug print routines */

void astProgramPrint(const Program *self, int indent, FILE *out) {
	STRUCT(
		Program,
		VEC_FIELD(items, astItemPrint(&self->items[i], indent, out))
	);
	
	putc('\n', out);
}

void astItemPrint(const Item *self, int indent, FILE *out) {
	switch (self->tag) {
	case ITEM_GLOBAL_VAR:
		CHOICE(GlobalVar, astVarDefPrint(&self->var_def, indent, out));
		break;
		
	case ITEM_FUNC:
		CHOICE(Func, astFuncDefPrint(&self->func_def, indent, out));
		break;
	}
}

void astFuncDefPrint(const FuncDef *self, int indent, FILE *out) {
	STRUCT(FuncDef, {
		FIELD(return_type, astDataTypePrint(&self->return_type, indent, out));
		STR_FIELD(ident);
		VEC_FIELD(params, astFuncParamPrint(&self->params[i], indent, out));
		VEC_FIELD(statements, astStmtPrint(&self->statements[i], indent, out));
	});
}

void astFuncParamPrint(const FuncParam *self, int indent, FILE *out) {
	STRUCT(FuncParam, {
		FIELD(data_type, astDataTypePrint(&self->data_type, indent, out));
		STR_FIELD(ident);
	});
}

void astStmtPrint(const Stmt *self, int indent, FILE *out) {
	switch (self->tag) {
	case STMT_EMPTY:
		CHOICE(Empty,);
		break;
		
	case STMT_IF:
		CHOICE(If, astIfStmtPrint(&self->if_stmt, indent, out));
		break;
		
	case STMT_FOR:
		CHOICE(For, astForStmtPrint(&self->for_stmt, indent, out));
		break;
		
	case STMT_WHILE:
		CHOICE(While, astWhileStmtPrint(&self->while_stmt, indent, out));
		break;
		
	case STMT_DO_WHILE:
		CHOICE(DoWhile, astWhileStmtPrint(&self->do_while_stmt, indent, out));
		break;
		
	case STMT_RETURN:
		CHOICE(Return, astExprPrint(&self->return_stmt, indent, out));
		break;
		
	case STMT_PRINT:
		CHOICE(Print, astPrintStmtPrint(&self->print_stmt, indent, out));
		break;
		
	case STMT_VAR_DEF:
		CHOICE(VarDef, astVarDefPrint(&self->var_def, indent, out));
		break;
		
	case STMT_ASSIGN:
		CHOICE(Assign, astAssignPrint(&self->assign, indent, out));
		break;
		
	case STMT_CALL:
		CHOICE(Call, astFuncCallPrint(&self->call, indent, out));
		break;
		
	case STMT_BLOCK:
		CHOICE(Block, astBlockPrint(&self->block, indent, out));
		break;
	}
}

void astBlockPrint(const Block *self, int indent, FILE *out) {
	STRUCT(
		Block,
		VEC_FIELD(statements, astStmtPrint(&self->statements[i], indent, out))
	);
}

void astPrintStmtPrint(const PrintStmt *self, int indent, FILE *out) {
	switch (self->tag) {
	case PRINT_STRING:
		CHOICE(String, fprintf(out, "\"%s\"", self->string));
		break;
		
	case PRINT_EXPR:
		CHOICE(Expr, astExprPrint(&self->expr, indent, out));
		break;
	}
}

void astIfStmtPrint(const IfStmt *self, int indent, FILE *out) {
	STRUCT(IfStmt, {
		FIELD(cond, astExprPrint(&self->cond, indent, out));
		FIELD(if_true, astStmtPrint(self->if_true, indent, out));
		FIELD(if_false, astStmtPrint(self->if_false, indent, out));
	});
}

void astWhileStmtPrint(const WhileStmt *self, int indent, FILE *out) {
	STRUCT(WhileStmt, {
		FIELD(cond, astExprPrint(&self->cond, indent, out));
		FIELD(body, astStmtPrint(self->body, indent, out));
	});
}

void astForStmtPrint(const ForStmt *self, int indent, FILE *out) {
	STRUCT(ForStmt, {
		FIELD(init, astForInitPrint(&self->init, indent, out));
		FIELD(cond, astExprPrint(&self->cond, indent, out));
		FIELD(update, astAssignPrint(&self->update, indent, out));
		FIELD(body, astStmtPrint(self->body, indent, out));
	});
}

void astForInitPrint(const ForInit *self, int indent, FILE *out) {
	switch (self->tag) {
	case FOR_INIT_VAR_DEF:
		CHOICE(VarDef, astVarDefPrint(&self->var_def, indent, out));
		break;
		
	case FOR_INIT_ASSIGN:
		CHOICE(Assign, astAssignPrint(&self->assign, indent, out));
		break;
	}
}

void astVarDefPrint(const VarDef *self, int indent, FILE *out) {
	STRUCT(VarDef, {
		FIELD(data_type, astDataTypePrint(&self->data_type, indent, out));
		FIELD(res_ident, astResIdentPrint(&self->res_ident, indent, out));
		FIELD(init, astExprPrint(&self->init, indent, out));
	});
}

void astExprPrint(const Expr *self, int indent, FILE *out) {
	switch (self->tag) {
	case EXPR_INVALID:
		CHOICE(None,);
		break;
		
	case EXPR_ASSIGN:
		CHOICE(Assign, {
			if (SEMANTIC_CHECK)
				fprintf(out, "%s, ", TYPE_NAMES[self->data_type]);
			astAssignPrint(&self->assign, indent, out);
		});
		break;
		
	case EXPR_BIN_OP:
		CHOICE(BinaryOp, {
			if (SEMANTIC_CHECK)
				fprintf(out, "%s, ", TYPE_NAMES[self->data_type]);
			astBinOpExprPrint(&self->bin_op, indent, out);
		});
		break;
		
	case EXPR_UNARY_MINUS:
		CHOICE(UnaryMinus, {
			if (SEMANTIC_CHECK)
				fprintf(out, "%s, ", TYPE_NAMES[self->data_type]);
			astExprPrint(self->unary_minus, indent, out);
		});
		break;
		
	case EXPR_CALL:
		CHOICE(Call, {
			if (SEMANTIC_CHECK)
				fprintf(out, "%s, ", TYPE_NAMES[self->data_type]);
			astFuncCallPrint(&self->call, indent, out);
		});
		break;
		
	case EXPR_LITERAL:
		CHOICE(Literal, {
			if (SEMANTIC_CHECK)
				fprintf(out, "%s, ", TYPE_NAMES[self->data_type]);
			astLiteralPrint(&self->literal, indent, out);
		});
		break;
		
	case EXPR_VAR:
		CHOICE(Var, {
			if (SEMANTIC_CHECK)
				fprintf(out, "%s, ", TYPE_NAMES[self->data_type]);
			astResIdentPrint(&self->var, indent, out);
		});
		break;
	}
}

void astFuncCallPrint(const FuncCall *self, int indent, FILE *out) {
	STRUCT(FuncCall, {
		FIELD(res_ident, astResIdentPrint(&self->res_ident, indent, out));
		VEC_FIELD(args, astExprPrint(&self->args[i], indent, out));
	});
}

void astAssignPrint(const Assign *self, int indent, FILE *out) {
	STRUCT(Assign, {
		FIELD(lhs, astResIdentPrint(&self->lhs, indent, out));
		FIELD(rhs, astExprPrint(self->rhs, indent, out));
	});
}

void astBinOpExprPrint(const BinOpExpr *self, int indent, FILE *out) {
	STRUCT(BinOpExpr, {
		FIELD(op, astBinOpPrint(&self->op, indent, out));
		FIELD(lhs, astExprPrint(self->lhs, indent, out));
		FIELD(rhs, astExprPrint(self->rhs, indent, out));
	});
}

void astBinOpPrint(const BinOp *self, int indent, FILE *out) {
	fputs(BIN_OP_NAMES[*self], out);
}

void astLiteralPrint(const Literal *self, int indent, FILE *out) {
	switch (self->tag) {
	case LITERAL_INT:
		CHOICE(Int, fprintf(out, "%i", self->iVal));
		break;
		
	case LITERAL_FLOAT:
		CHOICE(Float, fprintf(out, "%g", self->fVal));
		break;
		
	case LITERAL_BOOL:
		CHOICE(Bool, fprintf(out, "%s", self->bVal ? "true" : "false"));
		break;
	}
}

void astDataTypePrint(const DataType *self, int indent, FILE *out) {
	fputs(TYPE_NAMES[*self], out);
}

void astResIdentPrint(const ResIdent *self, int indent, FILE *out) {
	STRUCT(ResIdent, {
		STR_FIELD(ident);
		
		/* ignore the `res`-field to allow diffs with the non-semantically
		 * checked syntax tree even after semantic analysis  */
		
		if (SEMANTIC_CHECK) {
			FIELD(res, {
				if (defIdIsInvalid(self->res)) {
					fputs("(DefId) None", out);
				} else {
					fprintf(out, "(DefId) %u", self->res.index);
				}
			});
		}
	});
}
