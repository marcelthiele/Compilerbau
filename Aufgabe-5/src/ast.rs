//! The *abstract syntax tree* (AST) of C1 and interface to the LALRPOP-generated parser.
//!
//! # Overview
//!
//! The entry function of this module is [`parse`], which will take a string as input
//! and return the top-level AST node [`Program`].
//!
//! The hierarchy of the AST is roughly as follows:
//!
//! - [`Program`] is the root and contains [`Item`]s, which are either global variable
//!   or function definitions.
//! - Variable definitions have a type ([`DataType`]), a name ([`Ident`]) and an optional
//!   initializer expression ([`Expr`]).
//! - Function definition have a return type ([`DataType`]), a name ([`Ident`]), parameters
//!   ([`FuncParam`]), and a function body that contains statements ([`Stmt`]).
//! - Statements include control flow (e.g. [`IfStmt`], [`ForStmt`]), local variable
//!   definitions ([`VarDef`]), function calls ([`FuncCall`]) and assignments ([`Assign`]).
//! - The right hand side of variable definitions and assignments, and arguments to function
//!   calls are expressions ([`Expr`]).
//! - Expressions include literals ([`Literal`]), operations (e.g. [`BinOpExpr`]) and
//!   variable loads.
//!
//! # Name resolution ([`ResIdent`] and [`DefId`])
//!
//! Since we allow shadowing, an [`Ident`] alone does not uniquely identify a variable.
//! For example in this program there are three definitions of `x` and the print statement
//! should refer to the *innermost* of them:
//!
//! ```c
//! int x = 1;
//! void main() {
//!     int x = 2;
//!     {
//!         int x = 3;
//!         print(x);
//!     }
//! }
//! ```
//!
//! During interpretation, we need to know which memory location a variable access should
//! read from or write to. The process of finding out what variable an identifier refers
//! to is known as *name resolution* and happens after parsing during semantic analysis.
//!
//! For sake of simplicity, we want to interpret the AST directly, rather than *lowering*
//! (rewriting) the AST to an immediate representation first. Therefore, we need some extra
//! space in specific AST nodes to store which variable an identifier refers to.
//!
//! Resolvable identifiers ([`ResIdent`]s) provide this extra space: They store an optional
//! unique number of a definition ([`DefId`]) that the identifier refers to in addition to
//! the identifier itself. The parser will initially set all resolutions to `None` (with
//! [`ResIdent::new`]).
//!
//! During analysis, we will assign a unique [`DefId`] to every definition, including global
//! and local variables and functions. After resolving an identifier to a definition, the id
//! of the definition will be written directly into the AST (with [`ResIdent::set_res`]) and
//! can be retrieved from the AST by the interpreter (with [`ResIdent::get_res`]).
//!
//! # Examples
//!
//! Parsing a string into an AST:
//!
//! ```
//! use c1::ast;
//!
//! let input = "void main() {
//!     int answer = 42;
//!     print(answer);
//! }";
//!
//! let parsed_ast = ast::parse(input);
//!
//! let expected_ast = ast::Program {
//!     items: vec![ast::Item::Func(ast::FuncDef {
//!         return_type: ast::DataType::Void,
//!         ident: ast::Ident("main".to_owned()),
//!         params: vec![],
//!         statements: vec![
//!             ast::Stmt::VarDef(ast::VarDef {
//!                 data_type: ast::DataType::Int,
//!                 res_ident: ast::ResIdent::new(ast::Ident("answer".to_owned())),
//!                 init: Some(ast::Expr::Literal(ast::Literal::Int(42))),
//!             }),
//!             ast::Stmt::Print(ast::PrintStmt::Expr(ast::Expr::Var(
//!                 ast::ResIdent::new(ast::Ident("answer".to_owned()))
//!             ))),
//!         ],
//!     })]
//! };
//!
//! assert_eq!(parsed_ast, Ok(expected_ast));
//! ```

use std::borrow::Borrow;
use std::fmt::{self, Write};
use std::ops::{Deref, Index};

use lalrpop_util::lalrpop_mod;

use crate::lexer;

// This macro imports the parser generated by LALRPOP.
// It expands to a `mod parser` that contains a `struct ProgramParser`.
lalrpop_mod!(parser);

/// An error that occured during parsing.
pub type ParseError = lalrpop_util::ParseError<usize, lexer::Token, lexer::LexicalError>;

/// The top level parse function: It turns a string (`&str`) into an AST ([`Program`]).
pub fn parse(input: &str) -> Result<Program, ParseError> {
    let lexer = lexer::Lexer::new(input);
    let parser = parser::ProgramParser::new();
    parser.parse(lexer)
}

/// The data type of a variable or return type of a function: One of `void`, `bool`,
/// `int`, or `float`.
///
/// Note that `void` is syntactically valid as a data type of variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataType {
    Void,
    Bool,
    Int,
    Float,
}

impl DataType {
    /// Returns `true` if the data type is `int` or `float`.
    pub fn is_numeric(&self) -> bool {
        matches!(self, Self::Int | Self::Float)
    }
}

impl fmt::Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataType::Void => f.write_str("void"),
            DataType::Bool => f.write_str("bool"),
            DataType::Int => f.write_str("int"),
            DataType::Float => f.write_str("float"),
        }
    }
}

/// An identifier: The name of a variable or function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(pub String);

/// Prints the identifier in backticks.
impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{}`", self.0)
    }
}

/// This is used to index a `HashMap<Ident, X>` with `&str`.
impl Borrow<str> for Ident {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl Deref for Ident {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A unique identifier for the (function or variable) definition that a resolvable
/// identifier ([`ResIdent`]) resolves to.
///
/// This is necessary to distinguish between different variables with the same name
/// and will be used during analysis.
///
/// A `DefId` represents an index into a table of definitions that will be created
/// during analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefId(pub usize);

/// A resolvable identifier that references a (function or variable) definition.
#[derive(Debug, Clone, PartialEq)]
pub struct ResIdent {
    /// The name that is to be resolved.
    ident: Ident,
    /// The definition that this identifier resolves to.
    ///
    /// This field is written to during analysis and read from during interpretation.
    res: Option<DefId>,
}

impl ResIdent {
    /// Creates a new unresolved `ResIdent`.
    pub fn new(ident: Ident) -> Self {
        ResIdent { ident, res: None }
    }

    /// Stores the result of the resolution.
    ///
    /// This method will be called during analysis.
    ///
    /// # Panics
    ///
    /// Panics if this `ResIdent` was already resolved.
    pub fn set_res(&mut self, def_id: DefId) {
        assert!(self.res.is_none(), "already resolved: {self:?}");
        self.res = Some(def_id);
    }

    /// Loads the result of the resolution.
    ///
    /// This method will be called during interpretation.
    ///
    /// # Panics
    ///
    /// Panics if this `ResIdent` was not resolved.
    pub fn get_res(&self) -> DefId {
        self.res
            .unwrap_or_else(|| panic!("missing resolution for {self:?}"))
    }
}

impl fmt::Display for ResIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ident.fmt(f)
    }
}

impl Deref for ResIdent {
    type Target = Ident;

    fn deref(&self) -> &Self::Target {
        &self.ident
    }
}

/// Uniquely identifies an [`Item`] in a [`Program`] (AST).
///
/// The `ItemId` corresponds to the index of the item in the AST.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemId(pub usize);

/// Identifies a global variable item in [`Program`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GlobalVarItemId(pub ItemId);

/// Identifies a function item in [`Program`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuncItemId(pub ItemId);

/// The top-level node of the abstract syntax tree (AST) for a program.
///
/// Contains a list of top-level program elements, which can be either
/// global variable definitions, or function definitions.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    /// Indexed by [`ItemId`].
    pub items: Vec<Item>,
}

impl Index<ItemId> for Program {
    type Output = Item;

    fn index(&self, index: ItemId) -> &Self::Output {
        &self.items[index.0]
    }
}

impl Index<GlobalVarItemId> for Program {
    type Output = VarDef;

    /// Fetches the variable definition from the AST.
    fn index(&self, id: GlobalVarItemId) -> &Self::Output {
        match &self[id.0] {
            Item::GlobalVar(var_def) => var_def,
            item => unreachable!("expected {self:?} to be a global variable, found {item:?}"),
        }
    }
}

impl Index<FuncItemId> for Program {
    type Output = FuncDef;

    /// Fetches the function definition from the AST.
    fn index(&self, id: FuncItemId) -> &Self::Output {
        match &self[id.0] {
            Item::Func(func_def) => func_def,
            item => unreachable!("expected {self:?} to be a function, found {item:?}"),
        }
    }
}

/// A top-level program element: The definition of a global variable or function.
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    GlobalVar(VarDef),
    Func(FuncDef),
}

/// A function definition.
///
/// Includes the return type, a (non-resolvable) name, parameters, and the
/// function body as a list of statements.
///
/// # Example
///
/// ```c
/// int add(int x, int y) { return x + y; }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef {
    pub return_type: DataType,
    pub ident: Ident,
    pub params: Vec<FuncParam>,
    /// This is not a [`Block`], because the params are in the same scope.
    pub statements: Vec<Stmt>,
}

/// A function parameter with a type and a (non-resolvable) name.
#[derive(Debug, Clone, PartialEq)]
pub struct FuncParam {
    pub data_type: DataType,
    pub ident: Ident,
}

/// A function call. This can be a statement or expression.
///
/// Includes a resolvable function name and the arguments.
#[derive(Debug, Clone, PartialEq)]
pub struct FuncCall {
    pub res_ident: ResIdent,
    pub args: Vec<Expr>,
}

/// A variable definition. This can be a local or global variable, but not a function parameter.
///
/// Includes a data type, resolvable variable name, and optional initializer.
///
/// # Examples
///
/// with initializer:
///
/// ```c
/// int answer = 42;
/// ```
///
/// without initializer:
///
/// ```c
/// int uninit;
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct VarDef {
    pub data_type: DataType,
    /// Even though this is a definition, it still must be resolved to itself.
    /// This is needed to know the memory location that the `init` expression
    /// should be written to during interpretation.
    pub res_ident: ResIdent,
    /// The expression this variable is initialized with.
    pub init: Option<Expr>,
}

/// An assignment: `lhs = rhs`.
///
/// This can appear as a statement, expression, for initializer, or for update.
///
/// Includes a resolvable variable name (left) and an expression (right).
#[derive(Debug, Clone, PartialEq)]
pub struct Assign {
    /// Left hand side (the variable).
    pub lhs: ResIdent,
    /// Right hand side (the value).
    pub rhs: Box<Expr>,
}

/// A block of statements, which is itself a statement.
///
/// # Example
///
/// ```c
/// {
///     a = 1;
///     b = 2;
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub statements: Vec<Stmt>,
}

/// A statement.
///
/// Statements are the inner components of a function body, including control flow
/// variable definitions, assignments, and function calls.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// An empty statement, e.g. `;`.
    Empty,
    If(IfStmt),
    For(ForStmt),
    While(WhileStmt),
    DoWhile(WhileStmt),
    Return(Option<Expr>),
    Print(PrintStmt),
    VarDef(VarDef),
    Assign(Assign),
    Call(FuncCall),
    Block(Block),
}

/// An if statement: `if (cond) if_true else if_false`
#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub cond: Expr,
    pub if_true: Box<Stmt>,
    pub if_false: Option<Box<Stmt>>,
}

/// A for statement: `for (init; cond; update) body`
#[derive(Debug, Clone, PartialEq)]
pub struct ForStmt {
    pub init: ForInit,
    pub cond: Expr,
    pub update: Assign,
    pub body: Box<Stmt>,
}

/// The initialization (first) parameter of a for statement.
///
/// Can be either a variable definition or an assignment.
#[derive(Debug, Clone, PartialEq)]
pub enum ForInit {
    VarDef(VarDef),
    Assign(Assign),
}

/// A while or do-while statement: `while (cond) body` / `do body while (cond)`
#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub cond: Expr,
    pub body: Box<Stmt>,
}

/// A `print` statement, capable of printing strings or expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum PrintStmt {
    String(String),
    Expr(Expr),
}

/// An expression.
///
/// Expressions are the inner components of expressions that have a value,
/// including literals (e.g. `true`), unary or binary operations (e.g. `1 + 2`),
/// function calls, and variable references.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Assign(Assign),
    BinaryOp(BinOpExpr),
    UnaryMinus(Box<Expr>),
    Call(FuncCall),
    Literal(Literal),
    Var(ResIdent),
}

/// A binary operator, e.g. `+` or `!=`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    LogOr,
    LogAnd,
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => f.write_char('+'),
            BinOp::Sub => f.write_char('-'),
            BinOp::Mul => f.write_char('*'),
            BinOp::Div => f.write_char('/'),
            BinOp::LogOr => f.write_str("||"),
            BinOp::LogAnd => f.write_str("&&"),
            BinOp::Eq => f.write_str("=="),
            BinOp::Neq => f.write_str("!="),
            BinOp::Lt => f.write_char('<'),
            BinOp::Gt => f.write_char('>'),
            BinOp::Leq => f.write_str("<="),
            BinOp::Geq => f.write_str(">="),
        }
    }
}

/// A binary operation. Includes arithmetic, logic, and comparison.
///
/// Includes the operator and two expressions, e.g. `a + 1`.
#[derive(Debug, Clone, PartialEq)]
pub struct BinOpExpr {
    /// The operator.
    pub op: BinOp,
    /// Left hand side.
    pub lhs: Box<Expr>,
    // Right hand side.
    pub rhs: Box<Expr>,
}

/// A literal expression, e.g. `42` or `3.14` or `false`.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl Literal {
    /// Returns the type of the literal.
    pub fn data_type(&self) -> DataType {
        match self {
            Literal::Int(_) => DataType::Int,
            Literal::Float(_) => DataType::Float,
            Literal::Bool(_) => DataType::Bool,
        }
    }
}