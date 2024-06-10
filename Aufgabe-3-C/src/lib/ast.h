/***************************************************************************//**
 * @file ast.h
 * 
 * Der *abstrakte Syntaxbaum* (AST) von C1.
 *
 * # Überblick
 *
 * Die Hierarchie des ASTs sieht grob wie folgt aus:
 *
 * - `Program` ist die Wurzel und enthält `Item`s, welche entweder globale
 *   Variablen- oder Funktionsdefinitionen sind.
 * - Variablendefinitionen haben einen Typ (`DataType`), einen Namen (`Ident`)
 *   und einen optionalen Initialisierungsausdruck (`Expr`).
 * - Funktionsdefinitionen haben einen Rückgabetyp (`DataType`), einen Namen
 *   (`Ident`), Parameter (`FuncParam`) und einen Funktionskörper, der
 *   Anweisungen (`Stmt`) enthält.
 * - Anweisungen umfassen Kontrollstrukturen (z.B. `IfStmt`, `ForStmt`),
 *   lokale Variablendefinitionen (`VarDef`), Funktionsaufrufe (`FuncCall`) und
 *   Zuweisungen (`Assign`).
 * - Die rechte Seite von Variablendefinitionen und Zuweisungen sowie Argumente
 *   für Funktionsaufrufe sind Ausdrücke (`Expr`).
 * - Ausdrücke umfassen Literale (`Literal`), Operationen (z.B. `BinOpExpr`)
 *   und Variablenzugriffe.
 *
 * # Namensauflösung (`ResIdent` und `DefId`)
 *
 * Da wir das Überlagern von Namen erlauben, identifiziert ein `Ident` allein
 * nicht eindeutig eine Variable. Zum Beispiel gibt es in diesem Programm drei
 * Definitionen von `x`, und die Print-Anweisung sollte sich auf die
 * *innerste* davon beziehen:
 *
 * ```c
 * int x = 1;
 * void main() {
 *     int x = 2;
 *     {
 *         int x = 3;
 *         print(x);
 *     }
 * }
 * ```
 *
 * Während der Interpretation müssen wir wissen, aus welchem Speicherort eine
 * Variable gelesen oder in welchen sie geschrieben werden soll. Der Prozess
 * des Herausfindens, auf welche Variable sich ein Bezeichner bezieht, ist als
 * *Namensauflösung* bekannt und erfolgt nach dem Parsen während der
 * semantischen Analyse.
 *
 * Zur Vereinfachung wollen wir den AST direkt interpretieren, anstatt den AST
 * zunächst in eine Zwischenrepräsentation umzuwandeln. Daher benötigen wir in
 * bestimmten AST-Knoten zusätzlichen Platz, um zu speichern, auf welche
 * Variable sich ein Bezeichner bezieht.
 *
 * Auflösbare Bezeichner (`ResIdent`s) bieten diesen zusätzlichen Platz: Sie
 * speichern neben dem Bezeichner selbst optional eine eindeutige Nummer einer
 * Definition (`DefId`), auf die sich der Bezeichner bezieht. Der Parser setzt
 * alle Auflösungen zunächst auf `-1u`, was die Bedeutung von *nicht aufgelöst*
 * haben soll.
 *
 * Während der Analyse werden wir jeder Definition, einschließlich globaler und
 * lokaler Variablen und Funktionen, eine eindeutige `DefId` zuweisen. Nach
 * der Auflösung eines Bezeichners zu einer Definition wird die ID der
 * Definition direkt in den AST geschrieben und kann vom Interpreter aus dem
 * AST abgerufen werden.
 ******************************************************************************/

#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

/* *** Includes ************************************************************* */

#include <stdio.h>

/* *** Strukturen *********************************************************** */

/* Vorwärtsdeklaration von semantischen Definitionen */
typedef struct SymDef SymDef;

/**
 * Der Datentyp einer Variablen oder der Rückgabewert einer Funktion: Einer von
 * `void`, `bool`, `int` oder `float`.
 * 
 * Zu beachten ist, dass `void` syntaktisch als Datentyp von Variablen zulässig
 * ist.
 */
typedef enum {
	TYPE_VOID,
	TYPE_BOOL,
	TYPE_INT,
	TYPE_FLOAT
} DataType;

/** Ein binärer Operator, z.B. `+` oder `!=`. */
typedef enum {
	BIN_OP_ADD,
	BIN_OP_SUB,
	BIN_OP_MUL,
	BIN_OP_DIV,
	BIN_OP_LOG_OR,
	BIN_OP_LOG_AND,
	BIN_OP_EQ,
	BIN_OP_NEQ,
	BIN_OP_LT,
	BIN_OP_GT,
	BIN_OP_LEQ,
	BIN_OP_GEQ,
} BinOp;

/**
 * Eine eindeutige Kennung für die (Funktions- oder Variablen-)Definition, auf
 * die ein auflösbarer Bezeichner (`ResIdent`) verweist.
 *
 * Dies ist notwendig, um zwischen verschiedenen Variablen mit demselben Namen
 * zu unterscheiden, und wird während der Analyse verwendet.
 * 
 * Eine `DefId` stellt einen Index in einer Tabelle von Definitionen dar, die
 * während der Analyse erstellt wird.
 */
typedef struct {
	unsigned int index;
} DefId;

/**
 * Eine eindeutige Kennung für die Top-Level Elemente (`Item`) des abstrakten
 * Syntaxbaumes (`Program`).
 * 
 * Jede `ItemId` korrespondiert mit dem Index eines AST-Elementes.
 */
typedef struct {
	unsigned int index;
} ItemId;

/**
 * Ein auflösbarer Bezeichner, der auf eine (Funktions- oder Variablen-)
 * Definition verweist.
 */
typedef struct ResIdent {
	/** Der Name, der aufgelöst werden soll. */
	char *ident;
	
	/**
	 * Die Definition, auf die dieser Bezeichner verweist.
	 * 
     * Dieses Feld wird während der Analyse beschrieben und während der
	 * Interpretation gelesen.
	 */
	DefId res;
} ResIdent;

/** Ein Literal-Ausdruck, z.B. `42` oder `3.14` oder `false`. */
typedef struct Literal {
	enum {
		LITERAL_INT,
		LITERAL_FLOAT,
		LITERAL_BOOL
	} tag;
	
	union {
		int iVal;
		double fVal;
		int bVal;
	};
} Literal;

/**
 * Eine binäre Operation. Umfasst Arithmetik, Logik und Vergleich.
 *
 * Beinhaltet den Operator und zwei Ausdrücke, z.B. `a + 1`.
 */
typedef struct BinOpExpr {
	BinOp op;
	struct Expr *lhs;
	struct Expr *rhs;
} BinOpExpr;

/**
 * Eine Zuweisung: `lhs = rhs`.
 *
 * Erscheint in Form von Anweisung, Ausdruck, For-Initialisierung und
 * For-Update.
 *
 * Beinhaltet einen auflösbaren Variablennamen (links) und einen Ausdruck
 * (rechts).
 */
typedef struct Assign {
	/** Linke Seite (die Variable). */
	ResIdent lhs;
	/** Rechte Seite (der Wert). */
	struct Expr *rhs;
} Assign;

/**
 * Ein Funktionsaufruf. Dies kann eine Anweisung oder ein Ausdruck sein.
 *
 * Beinhaltet einen auflösbaren Funktionsnamen und die Argumente.
 */
typedef struct FuncCall {
	ResIdent res_ident;
	struct Expr *args;
} FuncCall;

/**
 * Ein Ausdruck.
 *
 * Ausdrücke sind die inneren Bestandteile von Ausdrücken, die einen Wert
 * haben, einschließlich Literale (z.B. `true`), unäre oder binäre Operationen
 * (z.B. `1 + 2`), Funktionsaufrufe und Variablenreferenzen.
 */
typedef struct Expr {
	enum {
		/**
		 * Enumerationsvariante für einen fehlenden Ausdruck.
		 * 
		 * Kann nur dort auftauchen, wo Ausdrücke optional sind, also bei der
		 * Initialisierung einer Variablen (`VarDef`) und bei der
		 * Funktionsrückgabe (Variante `STMT_RETURN` in `Stmt`).
		 */
		EXPR_INVALID = -1,
		EXPR_ASSIGN,
		EXPR_BIN_OP,
		EXPR_UNARY_MINUS,
		EXPR_CALL,
		EXPR_LITERAL,
		EXPR_VAR,
	} tag;
	
	/**
	 * Berechneter Datentyp des Ausdrucks.
	 * 
	 * Ergebnis der semantischen Analyse.
	 */
	DataType data_type;
	
	union {
		Assign assign;
		BinOpExpr bin_op;
		struct Expr *unary_minus;
		FuncCall call;
		Literal literal;
		ResIdent var;
	};
} Expr;

/**
 * Eine Variablendefinition. Dies kann eine lokale oder globale Variable sein,
 * jedoch kein Funktionsparameter.
 *
 * Beinhaltet einen Datentyp, einen auflösbaren Variablennamen und einen
 * optionalen Initialisierungsausdruck.
 *
 * # Beispiele
 *
 * mit Initialisierer:
 *
   ```c
   int answer = 42;
   ```
 *
 * ohne Initialisierer:
 *
   ```c
   int uninit;
   ```
 */
typedef struct VarDef {
	DataType data_type;
	
	/**
	 * Obwohl dies eine Definition ist, muss sie dennoch auf sich selbst
	 * aufgelöst werden. Dies ist notwendig, um den Speicherort zu ermitteln,
	 * in den der `init`-Ausdruck während der Interpretation geschrieben werden
	 * soll.
	 */
	ResIdent res_ident;
	
	/**
	 * Der Ausdruck, mit dem diese Variable initialisiert wird.
	 * 
	 * Liegt in Variante `EXPR_INVALID` vor, falls keine Initialisierung
	 * gewünscht ist.
	 */
	Expr init;
} VarDef;

/** Eine If-Anweisung: `if (cond) if_true else if_false` */
typedef struct IfStmt {
	Expr cond;
	struct Stmt *if_true;
	struct Stmt *if_false;
} IfStmt;

/**
 * Der Initialisierungsparameter einer For-Anweisung.
 *
 * Kann entweder eine Variablendefinition oder eine Zuweisung sein.
 */
typedef struct ForInit {
	enum {
		FOR_INIT_VAR_DEF,
		FOR_INIT_ASSIGN
	} tag;
	
	union {
		VarDef var_def;
		Assign assign;
	};
} ForInit;

/** Eine For-Anweisung: `for (init; cond; update) body` */
typedef struct ForStmt {
	ForInit init;
	Expr cond;
	Assign update;
	struct Stmt *body;
} ForStmt;

/**
 * Eine While- oder Do-While-Anweisung:
 * `while (cond) body` / `do body while (cond)`
 */
typedef struct WhileStmt {
	Expr cond;
	struct Stmt *body;
} WhileStmt;

/**
 * Eine `print`-Anweisung, die zur Ausgabe von Strings oder Ausdrücken genutzt
 * wird.
 */
typedef struct PrintStmt {
	enum {
		PRINT_STRING,
		PRINT_EXPR,
	} tag;
	
	union {
		char *string;
		Expr expr;
	};
} PrintStmt;

/**
 * Ein Block von Anweisungen, der selbst eine Anweisung ist.
 *
 * # Beispiel
 *
   ```c
   {
       a = 1;
       b = 2;
   }
   ```
 */
typedef struct Block {
	struct Stmt *statements;
} Block;

/**
 * Eine Anweisung.
 *
 * Anweisungen sind die inneren Bestandteile eines Funktionskörpers,
 * einschließlich Kontrollstrukturen, Variablendefinitionen, Zuweisungen und
 * Funktionsaufrufen.
 */
typedef struct Stmt {
	enum {
		/** Die leere Anweisung, z.B. `;`. */
		STMT_EMPTY,
		STMT_IF,
		STMT_FOR,
		STMT_WHILE,
		STMT_DO_WHILE,
		STMT_RETURN,
		STMT_PRINT,
		STMT_VAR_DEF,
		STMT_ASSIGN,
		STMT_CALL,
		STMT_BLOCK
	} tag;
	
	union {
		IfStmt if_stmt;
		ForStmt for_stmt;
		WhileStmt while_stmt;
		WhileStmt do_while_stmt;
		Expr return_stmt;
		PrintStmt print_stmt;
		VarDef var_def;
		Assign assign;
		FuncCall call;
		Block block;
	};
} Stmt;

/** Ein Funktionsparameter mit einem Typ und einem (nicht auflösbaren) Namen. */
typedef struct FuncParam {
	DataType data_type;
	char *ident;
} FuncParam;

/**
 * Eine Funktionsdefinition.
 *
 * Beinhaltet den Rückgabetyp, einen (nicht auflösbaren) Namen, Parameter und
 * den Funktionskörper als eine Liste von Anweisungen.
 *
 * # Beispiel
 *
   ```c
   int add(int x, int y) { return x + y; }
   ```
 */
typedef struct FuncDef {
	DataType return_type;
	char *ident;
	FuncParam *params;
	Stmt *statements;
} FuncDef;

/**
 * Ein Top-Level-Programmelement: Die Definition einer globalen Variable oder
 * Funktion.
 */
typedef struct Item {
	enum {
		ITEM_GLOBAL_VAR,
		ITEM_FUNC
	} tag;
	
	union {
		VarDef var_def;
		FuncDef func_def;
	};
} Item;

/**
 * Der oberste Knoten des abstrakten Syntaxbaums (AST) für ein Programm.
 *
 * Beinhaltet eine Liste von Top-Level-Programmelementen, die entweder
 * globale Variablendefinitionen oder Funktionsdefinitionen sein können.
 */
typedef struct Program {
	Item *items;
} Program;

/* *** Öffentliche Schnittstelle ******************************************** */

/* *** Konstruktorroutinen */

/**
 * Erzeugt ein neues, leeres `Program`-Objekt.
 * 
 * In diesem Objekt können mithilfe der Vektor-Schnittstelle weitere `Item`s
 * hinzugefügt werden.
 */
extern Program astProgramNew(void);

/**
 * Erstellt ein `Item` aus einer Variablendefinition.
 */
extern Item astItemFromVarDef(VarDef var_def);

/**
 * Erstellt ein `Item` aus einer Funktionsdefinition.
 */
extern Item astItemFromFuncDef(FuncDef func_def);

/**
 * Erstellt eine neue Funktionsdefinition.
 *
 * @param return_type Rückgabedatentyp der Funktion
 * @param ident       Name der Funktion
 * @param params      Vektor von Parametern der Funktion
 * @param statements  Vektor von Anweisungen im Funktionskörper
 * @return Ein neues `FuncDef`-Objekt.
 */
extern FuncDef astFuncDefNew(DataType return_type, char *ident, FuncParam *params, Stmt *statements);

/**
 * Erstellt einen neuen Funktionsaufruf.
 *
 * @param ident Name der Funktion
 * @param args  Vektor der Argumente des Funktionsaufrufs
 * @return Ein neues `FuncCall`-Objekt.
 */
extern FuncCall astFuncCallNew(char *ident, Expr *args);

/**
 * Erstellt einen neuen Funktionsparameter.
 *
 * @param data_type Datentyp des Parameters
 * @param ident     Name des Parameters
 * @return Ein neues `FuncParam`-Objekt.
 */
extern FuncParam astFuncParamNew(DataType data_type, char *ident);

/**
 * Erstellt einen Ausdruck aus einer Zuweisung.
 */
extern Expr astExprFromAssign(Assign assign);

/**
 * Erstellt einen Ausdruck aus einem Funktionsaufruf.
 */
extern Expr astExprFromFuncCall(FuncCall func_call);

/**
 * Erstellt einen Ausdruck aus einem Bezeichner.
 */
extern Expr astExprFromIdent(char *ident);

/**
 * Erstellt einen Ausdruck aus einem Literal.
 */
extern Expr astExprFromLiteral(Literal literal);

/**
 * Erstellt einen Ausdruck aus einem unären Minus-Ausdruck.
 */
extern Expr astExprFromUnaryMinus(Expr expr);

/**
 * Erstellt einen Ausdruck aus einem binären Operationausdruck.
 *
 * @param lval der linke Ausdruck
 * @param rval der rechte Ausdruck
 * @param op   der binäre Operator
 * @return Ein neues `Expr`-Objekt.
 */
extern Expr astExprFromBinOpExpr(Expr lval, Expr rval, BinOp op);

/**
 * Erstellt ein Literal aus einem Integer-Wert.
 */
extern Literal astLiteralFromInt(int value);

/**
 * Erstellt ein Literal aus einem Fließkomma-Wert.
 */
extern Literal astLiteralFromFloat(double value);

/**
 * Erstellt ein Literal aus einem Booleschen Wert.
 */
extern Literal astLiteralFromBool(int value);

/**
 * Erstellt eine neue Zuweisung.
 *
 * @param lhs linke Seite der Zuweisung
 * @param rhs Ausdruck, der zugewiesen wird
 * @return Ein neues `Assign`-Objekt.
 */
extern Assign astAssignNew(char *lhs, Expr rhs);

/**
 * Erstellt eine neue (leere) Anweisung.
 */
extern Stmt astStmtNew(void);

/**
 * Erstellt eine Anweisung aus einer If-Anweisung.
 */
extern Stmt astStmtFromIfStmt(IfStmt if_stmt);

/**
 * Erstellt eine Anweisung aus einer For-Anweisung.
 */
extern Stmt astStmtFromForStmt(ForStmt for_stmt);

/**
 * Erstellt eine Anweisung aus einer While-Anweisung.
 */
extern Stmt astStmtFromWhileStmt(WhileStmt while_stmt);

/**
 * Erstellt eine Anweisung aus einer Do-While-Anweisung.
 */
extern Stmt astStmtFromDoWhileStmt(WhileStmt do_while_stmt);

/**
 * Erstellt eine Anweisung aus einer Return-Anweisung.
 */
extern Stmt astStmtFromReturn(Expr *return_val);

/**
 * Erstellt eine Anweisung aus einer Print-Anweisung.
 */
extern Stmt astStmtFromPrintStmt(PrintStmt print_stmt);

/**
 * Erstellt eine Anweisung aus einer Variablendefinition.
 */
extern Stmt astStmtFromVarDef(VarDef var_def);

/**
 * Erstellt eine Anweisung aus einer Zuweisung.
 */
extern Stmt astStmtFromAssign(Assign assign);

/**
 * Erstellt eine Anweisung aus einem Funktionsaufruf.
 */
extern Stmt astStmtFromFuncCall(FuncCall call);

/**
 * Erstellt eine Anweisung aus einem Block.
 */
extern Stmt astStmtFromBlock(Block block);

/**
 * Erstellt eine neue If-Anweisung.
 *
 * @param cond     Bedingungsausdruck
 * @param if_true  Anweisungsteil, der bei erfüllter Bedingung ausgeführt wird
 * @param if_false Anweisungsteil, der bei nicht erfüllter Bedingung ausgeführt wird
 * @return Ein neues `IfStmt`-Objekt.
 */
extern IfStmt astIfStmtNew(Expr cond, Stmt if_true, Stmt if_false);

/**
 * Erstellt eine neue While-Anweisung.
 *
 * @param cond Bedingungsausdruck
 * @param body Anweisungsteil, der wiederholt wird
 * @return Ein neues `WhileStmt`-Objekt.
 */
extern WhileStmt astWhileStmtNew(Expr cond, Stmt body);

/**
 * Erstellt eine neue For-Anweisung.
 *
 * @param init   Initialisierungsanweisung
 * @param cond   Bedingungsausdruck
 * @param update Update-Anweisung
 * @param body   Anweisungsteil, der wiederholt wird
 * @return Ein neues `ForStmt`-Objekt.
 */
extern ForStmt astForStmtNew(ForInit init, Expr cond, Assign update, Stmt body);

/**
 * Erstellt eine For-Initialisierungsanweisung aus einer Variablendefinition.
 */
extern ForInit astForInitFromVarDef(VarDef var_def);

/**
 * Erstellt eine For-Initialisierungsanweisung aus einer Zuweisung.
 */
extern ForInit astForInitFromAssign(Assign assign);

/**
 * Erstellt eine Print-Anweisung aus einem String.
 */
extern PrintStmt astPrintStmtFromString(char *string);

/**
 * Erstellt eine Print-Anweisung aus einem Ausdruck.
 */
extern PrintStmt astPrintStmtFromExpr(Expr expr);

/**
 * Erstellt eine neue Variablendefinition.
 *
 * @param data_type Datentyp der Variablen
 * @param ident     Name der Variablen
 * @param init      Initialisierungsausdruck der Variablen
 * @return Ein neues `VarDef`-Objekt.
 */
extern VarDef astVarDefNew(DataType data_type, char *ident, Expr *init);

/**
 * Erstellt einen neuen Block von Anweisungen.
 *
 * @param statements Vektor mit Anweisungen
 * @return Ein neues `Block`-Objekt.
 */
extern Block astBlockNew(Stmt *statements);

/* *** Destruktorroutinen */

/**
 * Gibt den Speicher eines `Program`-Objekts frei.
 */
extern void astProgramRelease(Program *self);

/**
 * Gibt den Speicher eines `Item`-Objekts frei.
 */
extern void astItemRelease(Item *self);

/**
 * Gibt den Speicher eines `FuncDef`-Objekts frei.
 *
 * @param self Das `FuncDef`-Objekt.
 */
extern void astFuncDefRelease(FuncDef *self);

/**
 * Gibt den Speicher eines `FuncCall`-Objekts frei.
 */
extern void astFuncCallRelease(FuncCall *self);

/**
 * Gibt den Speicher eines `FuncParam`-Objekts frei.
 */
extern void astFuncParamRelease(FuncParam *self);

/**
 * Gibt den Speicher eines `Expr`-Objekts frei.
 */
extern void astExprRelease(Expr *self);

/**
 * Gibt den Speicher eines `Literal`-Objekts frei.
 */
extern void astLiteralRelease(Literal *self);

/**
 * Gibt den Speicher eines `Assign`-Objekts frei.
 */
extern void astAssignRelease(Assign *self);

/**
 * Gibt den Speicher eines `Stmt`-Objekts frei.
 */
extern void astStmtRelease(Stmt *self);

/**
 * Gibt den Speicher eines `IfStmt`-Objekts frei.
 */
extern void astIfStmtRelease(IfStmt *self);

/**
 * Gibt den Speicher eines `WhileStmt`-Objekts frei.
 */
extern void astWhileStmtRelease(WhileStmt *self);

/**
 * Gibt den Speicher eines `ForStmt`-Objekts frei.
 */
extern void astForStmtRelease(ForStmt *self);

/**
 * Gibt den Speicher eines `ForInit`-Objekts frei.
 */
extern void astForInitRelease(ForInit *self);

/**
 * Gibt den Speicher eines `PrintStmt`-Objekts frei.
 */
extern void astPrintStmtRelease(PrintStmt *self);

/**
 * Gibt den Speicher eines `VarDef`-Objekts frei.
 */
extern void astVarDefRelease(VarDef *self);

/**
 * Gibt den Speicher eines `Block`-Objekts frei.
 */
extern void astBlockRelease(Block *self);

/* *** Debug-Ausgaberoutinen */

/**
 * Gibt eine textuelle Darstellung eines `Program`-Objekts aus.
 *
 * @param self   das `Program`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astProgramPrint(const Program *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `Item`-Objekts aus.
 *
 * @param self   das `Item`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astItemPrint(const Item *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `FuncDef`-Objekts aus.
 *
 * @param self   das `FuncDef`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astFuncDefPrint(const FuncDef *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `FuncParam`-Objekts aus.
 *
 * @param self   das `FuncParam`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astFuncParamPrint(const FuncParam *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `Stmt`-Objekts aus.
 *
 * @param self   das `Stmt`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astStmtPrint(const Stmt *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `Block`-Objekts aus.
 *
 * @param self   das `Block`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astBlockPrint(const Block *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `PrintStmt`-Objekts aus.
 *
 * @param self   das `PrintStmt`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astPrintStmtPrint(const PrintStmt *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `WhileStmt`-Objekts aus.
 *
 * @param self   das `WhileStmt`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astWhileStmtPrint(const WhileStmt *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `ForStmt`-Objekts aus.
 *
 * @param self   das `ForStmt`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astForStmtPrint(const ForStmt *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `ForInit`-Objekts aus.
 *
 * @param self   das `ForInit`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astForInitPrint(const ForInit *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `IfStmt`-Objekts aus.
 *
 * @param self   das `IfStmt`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astIfStmtPrint(const IfStmt *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `VarDef`-Objekts aus.
 *
 * @param self   das `VarDef`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astVarDefPrint(const VarDef *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `Expr`-Objekts aus.
 *
 * @param self   das `Expr`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astExprPrint(const Expr *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `FuncCall`-Objekts aus.
 *
 * @param self   das `FuncCall`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astFuncCallPrint(const FuncCall *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `Assign`-Objekts aus.
 *
 * @param self   das `Assign`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astAssignPrint(const Assign *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `BinOpExpr`-Objekts aus.
 *
 * @param self   das `BinOpExpr`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astBinOpExprPrint(const BinOpExpr *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `BinOp`-Objekts aus.
 *
 * @param self   der binäre Operator
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astBinOpPrint(const BinOp *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `Literal`-Objekts aus.
 *
 * @param self   das `Literal`-Objekt
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astLiteralPrint(const Literal *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `DataType`-Objekts aus.
 *
 * @param self   der Datentyp
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astDataTypePrint(const DataType *self, int indent, FILE *out);

/**
 * Gibt eine textuelle Darstellung eines `ResIdent`-Objekts aus.
 *
 * @param self   der auflösbare Bezeichner
 * @param indent die Einrückungsebene
 * @param out    der Ausgabestream
 */
extern void astResIdentPrint(const ResIdent *self, int indent, FILE *out);

/**
 * Gibt `1` zurück, falls die übergebene `DefId` ungültig ist, ansonsten `0`.
 */
static inline int defIdIsInvalid(DefId self) {
	return self.index == -1u;
}

/**
 * Gibt `1` zurück, falls die übergebene `ItemId` ungültig ist, ansonsten `0`.
 */
static inline int itemIdIsInvalid(ItemId self) {
	return self.index == -1u;
}

/**
 * Array aller Typnamen zur verbesserten Debug-Ausgabe.
 */
extern const char *TYPE_NAMES[4];

/**
 * Array aller binären Operatoren zur verbesserten Debug-Ausgabe.
 */
extern const char *BIN_OP_NAMES[12];

/**
 * `DefId` einer ungültigen Referenz.
 */
extern const DefId INVALID_DEF_ID;

/**
 * `ItemId` einer ungültigen Referenz.
 */
extern const ItemId INVALID_ITEM_ID;

#endif
