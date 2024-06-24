//! The semantic analysis pass of C1.
//!
//! # Overview
//!
//! The entry point of the semantic analysis pass is the [`analyze`] function.
//! It is called on the AST root ([`ast::Program`]) after parsing and has the
//! following three goals:
//!
//! - Checking the static semantic of the program, i.e. performing all "compile-time"
//!   checks. For example, this includes checking whether the operands of an addition
//!   like `a + b` are compatible. If a static semantic rule is violated, [`analyze`]
//!   returns a human-readable error message in [`AnalysisError`].
//!
//! - Collecting auxiliary information about the definition of functions and variables
//!   that will be used by the interpreter. For example, this includes the size of the
//!   stack frame for every function, i.e. how many local variables it has. If no error
//!   occurs, [`analyze`] returns this information as [`ProgramInfo`].
//!
//! - Resolving all resolvable identifiers ([`ast::ResIdent`]s) to a definition. The
//!   resolutions are written directly into the AST with [`ast::ResIdent::set_res`].
//!
//! The central data type that powers our semantic analysis pass is the [`Analyzer`],
//! which uses its `visit_*` methods to traverses the AST in a depth-first manner,
//! similar to the [visitor pattern].
//!
//! [visitor pattern]: https://en.wikipedia.org/wiki/Visitor_pattern
//!
//! # Static semantic
//!
//! The full semantic rules are provided in a separate document. The analyzer checks
//! the rules in the `visit_*` methods and bubbles out the first error that it encounters
//! via the try (`?`) operator. We do not attempt error recovery.
//!
//! # Name resolution
//!
//! The analyzer uses a block-structured symbol table ([`Symtab`]) to do name
//! resolution.
//!
//! Scopes are crated and deleted with the [`Symtab::scope_enter`] and [`Symtab::scope_leave`]
//! functions. New symbols in the innermost scope are created with the `Symtab::define_*` family
//! of methods and symbols are resolved with the [`Symtab::resolve`] method.
//!
//! Calling `resolve` returns a `DefId`, which can be used as index into [`Analyzer`]
//! to retrieve additional information about the definition.
//!
//! # Examples
//!
//! This example demonstrates how to use the public API of this module: We use the auxiliary
//! information and resolved names produced by the semantic analysis to query some information
//! about our program:
//!
//! ```
//! use c1::{ast, analysis};
//!
//! let input = "void main() {
//!     int answer = 42;
//!     print(answer);
//! }";
//!
//! let mut ast = ast::parse(input).unwrap();
//! let analysis = analysis::analyze(&mut ast).unwrap();
//!
//! // How many local variables does main have?
//! let main_func_analysis = &analysis[analysis.main_func.unwrap()];
//! let main_locals = main_func_analysis.local_vars.len();
//! assert_eq!(main_locals, 1);
//!
//! // What definition did `answer` in `print(answer)` resolve to?
//! let main_func_item = &ast[main_func_analysis.item_id];
//! let ast::Stmt::Print(print_stmt) = &main_func_item.statements[1] else { unreachable!() };
//! let ast::PrintStmt::Expr(ast::Expr::Var(answer_res)) = print_stmt else { unreachable!() };
//! let answer_def_id = answer_res.get_res();
//! assert_eq!(answer_def_id, ast::DefId(1));
//!
//! // What memory location should `answer` in `print(answer)` be loaded from?
//! let answer_analysis = &analysis.definitions[answer_def_id];
//! // (The real interpreter should also handle `analysis::DefAnalysis::GlovalVar` here.)
//! let analysis::DefInfo::LocalVar(var_analysis) = answer_analysis else { unreachable!() };
//! assert_eq!(var_analysis.offset, 0);
//! ```
//!
//! Passing in an invalid program will produce an error:
//!
//! ```
//! use c1::{ast, analysis};
//!
//! let input = "void main() {
//!     int x = true;
//! }";
//!
//! let mut ast = ast::parse(input).unwrap();
//! let error = analysis::analyze(&mut ast).unwrap_err();
//! println!("{error}");
//! ```

use std::fmt;
use std::ops::Index;

pub use symtab::{DefInfo, Definitions, FuncDefId, FuncInfo, LocalVarDefId, Symtab, VarInfo};

use crate::ast;

mod symtab;

/// The entry function of the semantic analysis pass.
pub fn analyze(root: &mut ast::Program) -> Result<ProgramInfo, AnalysisError> {
    let mut analyser = Analyzer::default();

    for (index, item) in root.items.iter_mut().enumerate() {
        let item_id = ast::ItemId(index);
        analyser.visit_item(item_id, item)?;
    }
    let main_def_id = analyser.tab.resolve("main")?;

    // check if main is a function
    let main_func_info = match &analyser.tab[main_def_id] {
        DefInfo::Func(func_info) => func_info,
        _ => return Err(AnalysisError("main is not a function".to_string())),
    };

    // check return type
    if main_func_info.return_type != ast::DataType::Void {
        return Err(AnalysisError("main must return void".to_string()));
    }

    // check num of params
    if main_func_info.param_count != 0 {
        return Err(AnalysisError("main must have no parameters".to_string()));
    }

    let mut info = analyser.tab.into_program_info();

    info.main_func = Some(FuncDefId(main_def_id));

    Ok(info)
}

/// The visitor that drives the semantic analysis pass.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Analyzer {
    /// The block-structured symbol table.
    tab: Symtab,
}

impl Analyzer {
    /// Analyzes an item.
    fn visit_item(
        &mut self,
        item_id: ast::ItemId,
        item: &mut ast::Item,
    ) -> Result<(), AnalysisError> {
        match item {
            ast::Item::GlobalVar(var_def) => {
                self.visit_global_var_def(ast::GlobalVarItemId(item_id), var_def)
            }
            ast::Item::Func(func_def) => self.visit_func_def(ast::FuncItemId(item_id), func_def),
        }
    }

    /// Analyzes a global variable definition.
    fn visit_global_var_def(
        &mut self,
        _item_id: ast::GlobalVarItemId,
        var_def: &mut ast::VarDef,
    ) -> Result<(), AnalysisError> {
        self.visit_var_def(var_def, "global variable")?;

        // define global variable in global scope
        let def_id = self.tab
            .define_global_var(&var_def.res_ident, var_def.data_type, _item_id)?;

        // set resident of var_def.res_ident to def_id
        var_def.res_ident.set_res(def_id);
        

        Ok::<(), AnalysisError>(())
    }

    /// Analyzes a local variable definition (not a function parameter).
    fn visit_local_var_def(&mut self, var_def: &mut ast::VarDef) -> Result<(), AnalysisError> {
        self.visit_var_def(var_def, "local variable")?;

        // define local variable in current scope
        let def_id = self.tab
            .define_local_var(&var_def.res_ident, var_def.data_type)?;

        // set resident (resolve identifier) of var_def.res_ident to def_id, so that it can be resolved
        var_def.res_ident.set_res(def_id);

        Ok(())
    }

    /// Analyzes a variable definition.
    ///
    /// This method contains code that is shared between [`Self::visit_global_var_def`] and
    /// [`Self::visit_local_var_def`].
    ///
    /// The `kind` parameter can be used to distinguish global and local vars in diagnostics.
    fn visit_var_def(
        &mut self,
        var_def: &mut ast::VarDef,
        _kind: &str,
    ) -> Result<(), AnalysisError> {
        if let Some(init) = &mut var_def.init {
            let _expr_type = self.visit_expr(init)?;

            // check if _expr_type is the same as data_type of var_def (or if _expr_type can be converted to data_type (int -> float))
            if (var_def.data_type != _expr_type
                && !(var_def.data_type == ast::DataType::Float && _expr_type == ast::DataType::Int))
            {
                return Err(AnalysisError(format!(
                    "initialization of {} has wrong type",
                    _kind
                )));
            }
        }else if var_def.data_type == ast::DataType::Void {
            return Err(AnalysisError("variable cannot be void".to_string()));
        }

        Ok(())
    }

    /// Analyzes a function definition.
    fn visit_func_def(
        &mut self,
        _item_id: ast::FuncItemId,
        func_def: &mut ast::FuncDef,
    ) -> Result<(), AnalysisError> {
        // Define function name for global scope
        self.tab.define_func(
            func_def.ident.clone(),
            func_def.return_type,
            func_def.params.len(),
            _item_id,
        )?;

        // enter new scope
        self.tab.scope_enter();

        // define parameters in current scope
        for parameter in &func_def.params {
            self.visit_func_param(parameter)?;
        }

        // analyze function body
        for statement in &mut func_def.statements {
            self.visit_stmt(statement)?;
        }

        // leave scope
        self.tab.scope_leave();

        Ok(())
    }

    /// Analyzes a function parameter.
    fn visit_func_param(&mut self, _param: &ast::FuncParam) -> Result<(), AnalysisError> {
        // return error if parameter is void
        if _param.data_type == ast::DataType::Void {
            return Err(AnalysisError("parameter cannot be void".to_string()));
        }

        // define parameter in current scope
        self.tab.define_local_var(&_param.ident, _param.data_type)?;

        Ok(())
    }

    /// Analyzes a statement.
    fn visit_stmt(&mut self, stmt: &mut ast::Stmt) -> Result<(), AnalysisError> {
        match stmt {
            ast::Stmt::Empty => Ok(()),
            ast::Stmt::If(inner) => self.visit_if_stmt(inner),
            ast::Stmt::For(inner) => self.visit_for_stmt(inner),
            ast::Stmt::While(inner) => self.visit_while_stmt(inner, "while loop"),
            ast::Stmt::DoWhile(inner) => self.visit_while_stmt(inner, "do-while loop"),
            ast::Stmt::Return(expr) => self.visit_return_stmt(expr),
            ast::Stmt::Print(inner) => self.visit_print_stmt(inner),
            ast::Stmt::VarDef(var_def) => self.visit_local_var_def(var_def),
            ast::Stmt::Assign(assign) => {
                let _expr_type = self.visit_assign(assign)?;
                Ok(())
            }
            ast::Stmt::Call(call) => {
                let _expr_type = self.visit_call(call)?;
                Ok(())
            }
            ast::Stmt::Block(block) => self.visit_block(block),
        }
    }

    /// Analyzes a block statement.
    fn visit_block(&mut self, block: &mut ast::Block) -> Result<(), AnalysisError> {
        // enter scope
        self.tab.scope_enter();

        // analyze each statement in block
        for stmt in &mut block.statements {
            self.visit_stmt(stmt)?;
        }

        // leave scope
        self.tab.scope_leave();
        Ok(())
    }

    /// Analyzes an `if` statement.
    fn visit_if_stmt(&mut self, stmt: &mut ast::IfStmt) -> Result<(), AnalysisError> {
        self.visit_cond_expr(&mut stmt.cond, "if")?;
        self.visit_stmt(&mut stmt.if_true)?;
        if let Some(if_false) = &mut stmt.if_false {
            self.visit_stmt(if_false)?;
        }
        Ok(())
    }

    /// Analyzes a `for` statement.
    fn visit_for_stmt(&mut self, stmt: &mut ast::ForStmt) -> Result<(), AnalysisError> {
        // enter for scope
        self.tab.scope_enter();

        // get type of init (should be the same as type of update)
        let _init_type = match &mut stmt.init {
            ast::ForInit::VarDef(var_def) => {
                self.visit_local_var_def(var_def)?;
                var_def.data_type
            }
            ast::ForInit::Assign(assign) => self.visit_assign(assign)?,
        };

        let _update_type = self.visit_assign(&mut stmt.update)?;
        // check if _update_type is the same as _init_type (or if _update_type can be converted to _init_type (int -> float)
        if (_init_type != _update_type
            && !(_init_type == ast::DataType::Int && _update_type == ast::DataType::Float))
        {
            return Err(AnalysisError("init and update in for loop have different types".to_string()));
        }

        self.visit_cond_expr(&mut stmt.cond, "for loop")?;
        
        // analyze body of for loop
        self.visit_stmt(&mut stmt.body)?;

        // leave for scope
        self.tab.scope_leave();
        Ok(())
    }

    /// Analyzes a `while` or `do`-`while` statement.
    ///
    /// The `kind` parameter can be used to distinguish them in diagnostics.
    fn visit_while_stmt(
        &mut self,
        stmt: &mut ast::WhileStmt,
        kind: &str,
    ) -> Result<(), AnalysisError> {
        self.visit_cond_expr(&mut stmt.cond, kind)?;
        return self.visit_stmt(&mut stmt.body);
    }

    /// Analyzes a `return` statement.
    fn visit_return_stmt(&mut self, expr: &mut Option<ast::Expr>) -> Result<(), AnalysisError> {
        if let Some(expr) = expr {
            let _expr_type = self.visit_expr(expr)?;

            if let Some(func_info) = self.tab.current_func() {
                let return_type = func_info.return_type.clone();

                // check if _expr_type is the same as return_type of function (or if _expr_type can be converted to return_type (int -> float))
                if (func_info.return_type != _expr_type
                    && !(func_info.return_type == ast::DataType::Float && _expr_type == ast::DataType::Int))
                {
                    return Err(AnalysisError("return type does not match function return type".to_string()));
                }

                if return_type == ast::DataType::Void {
                    return Err(AnalysisError("cannot return value from void function".to_string()));
                }

                return Ok(());
            }
        }

        // if no expr -> check if return type of function is void
        if let Some(func_info) = self.tab.current_func() {
            if func_info.return_type != ast::DataType::Void {
                return Err(AnalysisError("return type does not match function return type".to_string()));
            }
        }
        Ok(())
    }

    /// Analyzes a `print` statement.
    fn visit_print_stmt(&mut self, print: &mut ast::PrintStmt) -> Result<(), AnalysisError> {
        match print {
            ast::PrintStmt::String(_) => Ok(()),
            ast::PrintStmt::Expr(expr) => {
                let _expr_type = self.visit_expr(expr)?;

                // check if _expr_type is void -> error
                if _expr_type == ast::DataType::Void {
                    return Err(AnalysisError("cannot print void".to_string()));
                }

                Ok(())
            },
        }
    }

    /// Analyzes a call statement or expression and returns its return type.
    fn visit_call(&mut self, call: &mut ast::FuncCall) -> Result<ast::DataType, AnalysisError> {
        for expr in &mut call.args {
            let _expr_type = self.visit_expr(expr)?;
        }

        // resolve function name
        let def_id = self.tab.resolve(&call.res_ident)?;

        call.res_ident.set_res(def_id);

        match &self.tab[def_id] {
            DefInfo::Func(func_info) => {
                // check number of params
                if call.args.len() != func_info.param_count {
                    return Err(AnalysisError("wrong number of arguments".to_string()));
                }
                // check if types of params are correct
                let return_type = func_info.return_type.clone();
                for (arg, expr) in &mut call.args.iter_mut().zip(func_info.local_vars.clone()) {
                    let arg_type = self.visit_expr(arg)?;
                    let param_type = self.tab[expr].data_type;
                    equal_types(arg_type, param_type)?;
                }
                // return return type of function
                Ok(return_type.clone())
            },
            _ => Err(AnalysisError("not a function".to_string())),
        }
        
    }

    /// Analyzes an assignment statement or expression and returns its type.
    fn visit_assign(&mut self, assign: &mut ast::Assign) -> Result<ast::DataType, AnalysisError> {
        let _rhs_type = self.visit_expr(&mut assign.rhs)?;

        let _def_id = self.tab.resolve(&mut assign.lhs)?;

        // set resident of lhs to def_id
        assign.lhs.set_res(_def_id);

        let _lhs_type = match &self.tab[_def_id] {
            DefInfo::LocalVar(var_info) => Ok::<_, AnalysisError>(var_info.data_type),
            DefInfo::GlobalVar(var_info) => Ok::<_, AnalysisError>(var_info.data_type),
            _ => return Err(AnalysisError("lhs is not a variable".to_string())),
        }?;

        // check if _lhs_type is the same as _rhs_type (or if _rhs_type can be converted to _lhs_type (int -> float))
        if (_lhs_type != _rhs_type
            && !(_lhs_type == ast::DataType::Float && _rhs_type == ast::DataType::Int))
        {
            return Err(AnalysisError(
                "lhs and rhs have different types".to_string(),
            ));
        }

        Ok(_lhs_type)
    }

    /// Analyzes the condition expression of a control flow statement, expecting
    /// a boolean type.
    ///
    /// The `kind` parameter describes the statement for diagnostics.
    fn visit_cond_expr(&mut self, expr: &mut ast::Expr, _kind: &str) -> Result<(), AnalysisError> {
        let _cond_type = self.visit_expr(expr)?;

        // check if _cond_type is boolean
        equal_types(_cond_type, ast::DataType::Bool)?;
        Ok(())
    }

    /// Analyzes an expression and returns its type.
    fn visit_expr(&mut self, expr: &mut ast::Expr) -> Result<ast::DataType, AnalysisError> {
        match expr {
            ast::Expr::BinaryOp(inner) => self.visit_bin_op_expr(inner),
            ast::Expr::UnaryMinus(inner) => self.visit_unary_minus_expr(inner),
            ast::Expr::Assign(inner) => self.visit_assign(inner),
            ast::Expr::Call(inner) => self.visit_call(inner),
            ast::Expr::Literal(literal) => Ok(literal.data_type()),
            ast::Expr::Var(res_ident) => self.visit_var_expr(res_ident),
        }
    }

    /// Analyzes a binary operator expression and returns its type.
    fn visit_bin_op_expr(
        &mut self,
        bin_op_expr: &mut ast::BinOpExpr,
    ) -> Result<ast::DataType, AnalysisError> {
        let _lhs_type = self.visit_expr(&mut bin_op_expr.lhs)?;
        let _rhs_type = self.visit_expr(&mut bin_op_expr.rhs)?;


        // if lhs or rhs is void -> error
        if _lhs_type == ast::DataType::Void || _rhs_type == ast::DataType::Void {
            return Err(AnalysisError("cannot use void in binary operation".to_string()));
        }

        equal_types(_lhs_type, _rhs_type)?;

        match bin_op_expr.op {
            ast::BinOp::Add | ast::BinOp::Sub | ast::BinOp::Mul | ast::BinOp::Div => {
                if _lhs_type == ast::DataType::Bool {
                    return Err(AnalysisError("expected type int or float".to_string()));
                }
                return Ok(_lhs_type);
            }
            ast::BinOp::LogAnd | ast::BinOp::LogOr => {
                if _lhs_type != ast::DataType::Bool {
                    return Err(AnalysisError("expected type bool".to_string()));
                }
                return Ok(_lhs_type);
            }
            ast::BinOp::Eq | ast::BinOp::Neq | ast::BinOp::Lt | ast::BinOp::Leq | ast::BinOp::Gt | ast::BinOp::Geq => {
                // if _lhs_type == ast::DataType::Bool {
                //     return Err(AnalysisError("expected type int or float".to_string()));
                // }
                return Ok(ast::DataType::Bool);
            }
        }

    }

    /// Analyzes an unary minus expression and returns its type.
    fn visit_unary_minus_expr(
        &mut self,
        inner_expr: &mut ast::Expr,
    ) -> Result<ast::DataType, AnalysisError> {
        let _expr_type = self.visit_expr(inner_expr)?;

        if(_expr_type != ast::DataType::Int && _expr_type != ast::DataType::Float) {
            return Err(AnalysisError("expected type int or float".to_string()));
        }

        Ok(_expr_type)
    }

    /// Analyzes a variable expression and returns its type.
    fn visit_var_expr(
        &mut self,
        _res_ident: &mut ast::ResIdent,
    ) -> Result<ast::DataType, AnalysisError> {
        let _def_id = self.tab.resolve(_res_ident)?;

        _res_ident.set_res(_def_id);

        match &self.tab[_def_id] {
            DefInfo::LocalVar(var_info) => Ok(var_info.data_type),
            DefInfo::GlobalVar(var_info) => Ok(var_info.data_type),
            _ => Err(AnalysisError("not a variable".to_string())),
        }
    }
}

/// Compares two types and returns the common type if they are compatible.
fn equal_types(lhs: ast::DataType, rhs: ast::DataType) -> Result<(ast::DataType), AnalysisError> {
    if lhs == rhs {
        return Ok(lhs);
    } else if ((lhs == ast::DataType::Int && rhs == ast::DataType::Float)
        || (lhs == ast::DataType::Float && rhs == ast::DataType::Int))
    {
        return Ok(ast::DataType::Float);
    } else {
        return Err(AnalysisError(format!(
            "expected type {:?}, found type {:?}",
            lhs, rhs
        )));
    }
}

/// The top-level type that contains all program information that is collected during analysis.
///
/// Contains information about the main function and global variables that is required
/// for program startup, as well as the cumulative information collected for all definitions.
///
/// The structure can be accessed by the index operator. Providing a more specific
/// kind of id will return a more specific kind of result:
///
/// ```
/// use c1::ast::DefId;
/// use c1::analysis::*;
///
/// fn get_any(definitions: &ProgramInfo, id: DefId) -> &DefInfo {
///     &definitions[id]
/// }
///
/// fn get_func(definitions: &ProgramInfo, id: FuncDefId) -> &FuncInfo {
///     &definitions[id]
/// }
///
/// fn get_local_var(definitions: &ProgramInfo, id: LocalVarDefId) -> &VarInfo {
///     &definitions[id]
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ProgramInfo {
    pub definitions: Definitions,
    pub global_vars: Vec<ast::GlobalVarItemId>,
    pub main_func: Option<FuncDefId>,
}

impl Index<ast::DefId> for ProgramInfo {
    type Output = DefInfo;

    fn index(&self, id: ast::DefId) -> &Self::Output {
        &self.definitions[id]
    }
}

impl Index<LocalVarDefId> for ProgramInfo {
    type Output = VarInfo;

    fn index(&self, id: LocalVarDefId) -> &Self::Output {
        &self.definitions[id]
    }
}

impl Index<FuncDefId> for ProgramInfo {
    type Output = FuncInfo;

    fn index(&self, id: FuncDefId) -> &Self::Output {
        &self.definitions[id]
    }
}

/// A human-readable compile-time error.
#[derive(Debug, Clone, PartialEq)]
pub struct AnalysisError(String);

impl fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<symtab::DefineError> for AnalysisError {
    fn from(err: symtab::DefineError) -> Self {
        let msg = format!("duplicate definition of {} in the same scope", err.0);
        AnalysisError(msg)
    }
}

impl From<symtab::ResolveError> for AnalysisError {
    fn from(err: symtab::ResolveError) -> Self {
        let msg = format!("cannot resolve {} in this scope", err.0);
        AnalysisError(msg)
    }
}
