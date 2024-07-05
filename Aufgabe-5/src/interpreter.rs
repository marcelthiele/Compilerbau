//! The interpreter that executes C1 programs.
//!
//! This module contains the implementation of the interpreter that uses the
//! abstract syntax tree (AST) as well as the information calculated during
//! the semantic analysis to run a C1 program.
//!
//! It utilizes a virtual machine ([`VirtualMachine`]) helper to maintain the
//! state required for interpreting the AST, including managing global variables,
//! the function call stack (including local variables), and return values.
//!
//! The entry point for interpretation is the [`interpret`] function, which
//! initializes the interpreter, sets up global variables, and visits the main
//! function of the program.
//!
//! The module also defines the [`Interpreter`] structure, which provides
//! methods to visit and evaluate statements and expressions in the AST, handle
//! function calls, and manage control flow constructs such as loops and
//! conditionals.
//!
//! Additionally, the module defines the [`InterpretError`] structure for
//! communicating errors that occur during interpretation.

#![allow(dead_code)]

use std::{fmt::{self, Write}, ptr::null};

use crate::{analysis, ast};
use vm::{Value, Variable, VirtualMachine};

mod vm;

/// The entry function of the interpretation.
///
/// This function initializes the interpreter with the given AST and program
/// information, sets up the global variables, and visits the main function.
pub fn interpret(
    ast: &ast::Program,
    info: &analysis::ProgramInfo,
) -> Result<String, InterpretError> {
    let mut interpreter = Interpreter {
        ast,
        info,
        output: String::new(),
        vm: VirtualMachine::new(info.global_vars.len()),
    };

    // initialize the global variables in declaration order
    for &item_id in &info.global_vars {
        interpreter.visit_var_def(&ast[item_id])?;
    }

    // visit the main function
    let mut res_ident = ast::ResIdent::new(ast::Ident("main".to_owned()));
    res_ident.set_res(info.main_func.unwrap().0);
    interpreter.visit_func_call(&ast::FuncCall {
        res_ident,
        args: Vec::new(),
    })?;

    // return the resulting output
    Ok(interpreter.output)
}

/// Computes the *least upper bound* (LUB) of two types.
///
/// Given two types `a` and `b`, the LUB is a type `c`, such that
/// - both `a` and `b` can be cast to `c`, and
/// - `c` is the *most concrete* type that satisfies this property.
fn least_upper_bound(lhs: ast::DataType, rhs: ast::DataType) -> ast::DataType {
    use ast::DataType::*;
    match (lhs, rhs) {
        (a, b) if a == b => a,
        (Int, Float) | (Float, Int) => Float,
        (a, b) => unreachable!("invalid LUB of `{a:?}` and `{b:?}`"),
    }
}

/// Structure representing the interpreter.
///
/// This structure holds the state required for interpreting the AST, including
/// the AST, program information, output string, and the virtual machine storing
/// the variables.
#[derive(Debug, Clone, PartialEq)]
struct Interpreter<'a> {
    ast: &'a ast::Program,
    info: &'a analysis::ProgramInfo,
    output: String,
    vm: VirtualMachine,
}

impl Interpreter<'_> {
    /// Visits a statement.
    fn visit_stmt(&mut self, stmt: &ast::Stmt) -> Result<(), InterpretError> {
        use ast::Stmt::*;
        match stmt {
            Empty => Ok(()),
            If(inner) => self.visit_if_stmt(inner),
            For(inner) => self.visit_for_stmt(inner),
            While(inner) => self.visit_while_stmt(inner),
            DoWhile(inner) => self.visit_do_while_stmt(inner),
            Return(expr) => self.visit_return_stmt(expr),
            Print(inner) => self.visit_print_stmt(inner),
            VarDef(var_def) => self.visit_var_def(var_def),
            Assign(assign) => self.visit_assign(assign).map(|_| ()),
            Call(call) => self.visit_func_call(call).map(|_| ()),
            Block(block) => self.visit_block(block),
        }
    }

    /// Visits an expression and evaluates it.
    fn visit_expr(&mut self, expr: &ast::Expr) -> Result<Value, InterpretError> {
        use ast::Expr::*;
        match expr {
            BinaryOp(inner) => self.visit_bin_op_expr(inner),
            UnaryMinus(inner) => self.visit_unary_minus(inner),
            Assign(assign) => self.visit_assign(assign),
            Call(inner) => self.visit_func_call_expr(inner),
            Literal(literal) => Ok(literal.clone().into()),
            Var(res_ident) => self.visit_load_var(res_ident),
        }
    }

    /// Visits an `if` statement.
    fn visit_if_stmt(&mut self, stmt: &ast::IfStmt) -> Result<(), InterpretError> {
        // todo!("evaluate conditional");
        self.visit_expr(&stmt.cond)?;
        self.visit_stmt(&stmt.if_true)?;
        if let Some(if_false) = &stmt.if_false {
            self.visit_stmt(if_false)?;
        }

        Ok(())
    }

    /// Visits a `for` statement.
    fn visit_for_stmt(&mut self, _stmt: &ast::ForStmt) -> Result<(), InterpretError> {
        // todo!("evaluate initializer, run the body and update until the condition evaluates to false or the function seeks to return");
        

        match &_stmt.init {
            ast::ForInit::VarDef(var_def) => self.visit_var_def(var_def)?,
            ast::ForInit::Assign(assign) => {
                // Ignore the expression type.
                self.visit_assign(assign)?;
            }
        }

        self.visit_expr(&_stmt.cond)?;
        self.visit_assign(&_stmt.update)?;
        self.visit_stmt(&_stmt.body)?;
        
        Ok(())
    }

    /// Visits a `while` statement.
    fn visit_while_stmt(&mut self, _stmt: &ast::WhileStmt) -> Result<(), InterpretError> {
        todo!(
            "run the body until the condition evaluates to false or the function seeks to return"
        );
    }

    /// Visits a `do-while` statement.
    fn visit_do_while_stmt(&mut self, _stmt: &ast::WhileStmt) -> Result<(), InterpretError> {
        todo!("run the body at least once and then until the condition evaluates to false or the function seeks to return");
    }

    /// Visits a `return` statement, setting the return value.
    fn visit_return_stmt(&mut self, _expr: &Option<ast::Expr>) -> Result<(), InterpretError> {
        // todo!("set the return flag and return value if applicable");

        if let Some(expr) = _expr {
            let value = self.visit_expr(expr)?;
            self.vm.set_return(Some(value));
            Ok(())
        } else {
            self.vm.set_return(None);
            Ok(())
        }
    }

    /// Visits a `print` statement, writing into the output string.
    fn visit_print_stmt(&mut self, print: &ast::PrintStmt) -> Result<(), InterpretError> {
        match print {
            ast::PrintStmt::String(string) => {
                writeln!(self.output, "{string}").unwrap();
                Ok(())
            }
            ast::PrintStmt::Expr(_expr) => {
                todo!("evaluate the expression and print it, also taking care of special float values");
            }
        }
    }

    /// Visits a variable definition and initializes it if possible.
    fn visit_var_def(&mut self, var_def: &ast::VarDef) -> Result<(), InterpretError>{
        // todo!("initialize the variable according to its definition, if applicable");

        let def_id = var_def.res_ident.get_res();
        let def_info = &self.info.definitions[def_id];

        if let Some(expr) = &var_def.init {
            let value = self.visit_expr(expr)?;
            
            self.vm.store_var(def_info, value);

            Ok(())
        } else {
            let none_value = match def_info {
                analysis::DefInfo::GlobalVar(_) => Value::Int(0),
                analysis::DefInfo::LocalVar(_) => Value::Int(0),
                _ => panic!("Attempted to initialize a function"),
            };
            self.vm.store_var(def_info, none_value);
            // TODO eigentlich sollte man hier nicht mit 0 initialisieren, sondern ohne Wert initialisieren

            Ok(())
        }

    }

    /// Visits a block of statements and evaluates each one.
    fn visit_block(&mut self, _block: &ast::Block) -> Result<(), InterpretError> {
        // todo!("visit the contained statements or return early if requested");




        for stmt in &_block.statements {
            self.visit_stmt(stmt)?;
            if self.vm.is_returning() {
                break;
            }
        }

        

        Ok(())
    }

    /// Visits a function call and evaluates it.
    fn visit_func_call(&mut self, call: &ast::FuncCall) -> Result<Variable, InterpretError> {
        // TODO: 1. Evaluate the arguments.

        call.args.iter().for_each(|arg| {
            self.visit_expr(arg).unwrap();
        });

        // TODO: 2. Reserve space for the local variables and initialize the
        //          parameters with the argument values.
        // let locals = vec![Variable::Uninit; self.info.definitions[call.res_ident.get_res()]];
        // self.vm.push_frame(locals);

        // TODO: 3. Setup and later restore the stack-frame.

        // TODO: 4. Extract the return value.

        let def_id = call.res_ident.get_res();
        let func_info = match &self.info.definitions[def_id] {
            analysis::DefInfo::Func(info) => info,
            _ => unreachable!("function call resolves to non-function"),
        };
        let func_def = &self.ast[func_info.item_id];

        // Evaluate the function body.
        for stmt in &func_def.statements {
            self.visit_stmt(stmt)?;
            if self.vm.is_returning() {
                break;
            }
        }

        Ok(self.vm.take_return())
    }

    /// Visits a binary operation expression and evaluates it.
    fn visit_bin_op_expr(
        &mut self,
        _bin_op_expr: &ast::BinOpExpr,
    ) -> Result<Value, InterpretError> {
        // todo!("evaluate both operands and perform the operation, taking special care of potential integer overflow");

        let lhs = self.visit_expr(&_bin_op_expr.lhs)?;
        let rhs = self.visit_expr(&_bin_op_expr.rhs)?;

        match _bin_op_expr.op {
            ast::BinOp::Add => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs.checked_add(rhs);

                        // if res is None -> overflow -> throw error
                        if res == None{
                            return Err(InterpretError("Overflow".to_owned()));
                        }

                        Ok(Value::Int(res.unwrap()))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs + rhs;
                        Ok(Value::Float(res))
                    },
                    _ => Err(InterpretError("Invalid types for addition".to_owned()))
                }
            },
            ast::BinOp::Sub => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs.checked_sub(rhs);

                        // if res is None -> overflow -> throw error
                        if res == None{
                            return Err(InterpretError("Overflow".to_owned()));
                        }


                        Ok(Value::Int(res.unwrap()))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs - rhs;
                        Ok(Value::Float(res))
                    },
                    _ => Err(InterpretError("Invalid types for subtraction".to_owned()))
                }
            },
            ast::BinOp::Mul => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs.checked_mul(rhs);

                        // if res is None -> overflow -> throw error
                        if res == None{
                            return Err(InterpretError("Overflow".to_owned()));
                        }

                        Ok(Value::Int(res.unwrap()))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs * rhs;
                        Ok(Value::Float(res))
                    },
                    _ => Err(InterpretError("Invalid types for multiplication".to_owned()))
                }
            },
            ast::BinOp::Div => {
                if rhs == Value::Int(0) || rhs == Value::Float(0.0) {
                    // Interpreter error: division by zero
                    return Err(InterpretError("Division by zero".to_owned()));
                }
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs.checked_div(rhs);

                        // if res is None -> overflow -> throw error
                        if res == None{
                            return Err(InterpretError("Overflow".to_owned()));
                        }

                        Ok(Value::Int(res.unwrap()))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs / rhs;
                        Ok(Value::Float(res))
                    },
                    _ => Err(InterpretError("Invalid types for division".to_owned()))
                }
            },
            ast::BinOp::LogAnd => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs & rhs;
                        Ok(Value::Int(res))
                    },
                    _ => Err(InterpretError("Invalid types for bitwise and".to_owned()))
                }
            },
            ast::BinOp::LogOr => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs | rhs;
                        Ok(Value::Int(res))
                    },
                    _ => Err(InterpretError("Invalid types for bitwise or".to_owned()))
                }
            },
            ast::BinOp::Eq => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs == rhs;
                        Ok(Value::Bool(res))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs == rhs;
                        Ok(Value::Bool(res))
                    },
                    _ => Err(InterpretError("Invalid types for equality".to_owned()))
                }
            },
            ast::BinOp::Neq => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs != rhs;
                        Ok(Value::Bool(res))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs != rhs;
                        Ok(Value::Bool(res))
                    },
                    _ => Err(InterpretError("Invalid types for inequality".to_owned()))
                }
            },
            ast::BinOp::Lt => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs < rhs;
                        Ok(Value::Bool(res))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs < rhs;
                        Ok(Value::Bool(res))
                    },
                    _ => Err(InterpretError("Invalid types for less than".to_owned()))
                }
            },
            ast::BinOp::Leq => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs <= rhs;
                        Ok(Value::Bool(res))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs <= rhs;
                        Ok(Value::Bool(res))
                    },
                    _ => Err(InterpretError("Invalid types for less than or equal".to_owned()))
                }
            },
            ast::BinOp::Gt => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs > rhs;
                        Ok(Value::Bool(res))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs > rhs;
                        Ok(Value::Bool(res))
                    },
                    _ => Err(InterpretError("Invalid types for greater than".to_owned()))
                }
            },
            ast::BinOp::Geq => {
                match (lhs, rhs) {
                    (Value::Int(lhs), Value::Int(rhs)) => {
                        let res = lhs >= rhs;
                        Ok(Value::Bool(res))
                    },
                    (Value::Float(lhs), Value::Float(rhs)) => {
                        let res = lhs >= rhs;
                        Ok(Value::Bool(res))
                    },
                    _ => Err(InterpretError("Invalid types for greater than or equal".to_owned()))
                }
            },
        }
    }

    /// Visits a unary minus expression and evaluates it.
    fn visit_unary_minus(&mut self, _inner_expr: &ast::Expr) -> Result<Value, InterpretError> {
        // Evaluate the operand.
        let inner = self.visit_expr(_inner_expr)?;

        match inner {
            // Handle integer case with checked_neg to prevent overflow.
            Value::Int(inner) => {
                match inner.checked_neg() {
                    Some(neg_value) => Ok(Value::Int(neg_value)),
                    None => Err(InterpretError("Integer overflow".to_owned())),
                }
            },
            // Floating-point negation does not overflow, directly negate.
            Value::Float(inner) => Ok(Value::Float(-inner)),
            // Error for unsupported types.
            _ => Err(InterpretError("Invalid type for unary minus".to_owned())),
        }
    }


    /// Visits an assignment expression and evaluates it.
    fn visit_assign(&mut self, _assign: &ast::Assign) -> Result<Value, InterpretError> {
        // todo!("evaluate the right-hand-side and store the result in the variable referred to by the left-hand-side");

        let rhs = self.visit_expr(&_assign.rhs)?;
        // let lhs = self.ast[_assign.lhs];

        let def_id = _assign.lhs.get_res();
        let def_info = &self.info.definitions[def_id];
        Ok(self.vm.store_var(def_info, rhs))
    }

    /// Visits a function call expression and evaluates it.
    fn visit_func_call_expr(&mut self, _call: &ast::FuncCall) -> Result<Value, InterpretError> {
        // todo!("evaluate the function call, returning its (non-void) result");

        let def_id = _call.res_ident.get_res();
        let func_info = match &self.info.definitions[def_id] {
            analysis::DefInfo::Func(info) => info,
            _ => unreachable!("function call resolves to non-function"),
        };

        let func_def = &self.ast[func_info.item_id];

        // Evaluate the function body.
        for stmt in &func_def.statements {
            self.visit_stmt(stmt)?;
            if self.vm.is_returning() {
                // return Ok(self.vm.take_return());
                // break;
            }
        };

        let var = self.vm.take_return();
        match var {
            Variable::Init(value) => Ok(value),
            Variable::Uninit => panic!("Attempted to read an uninitialized variable"),
        }

    }

    /// Visits a variable and loads its value.
    fn visit_load_var(&mut self, _ident: &ast::ResIdent) -> Result<Value, InterpretError> {
        // todo!("read the value of the variable, taking care not to read an uninitialized value");

        let def_id = _ident.get_res();
        let def_info = &self.info.definitions[def_id];

        let ret = self.vm.load_var(def_info);

        let value = match ret {
            Variable::Init(value) => value,
            Variable::Uninit => panic!("Attempted to read an uninitialized variable"),
        };

        Ok(value)
    }
}

/// Structure representing an interpretation error.
///
/// This structure holds a human-readable error message string.
#[derive(Debug, Clone, PartialEq)]
pub struct InterpretError(String);

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
