//! This module provides the [`Calculator`] struct, which is designed to
//! evaluate arithmetic expressions parsed into a [`Root`] structure from a
//! string representation. It supports operations including addition,
//! subtraction, multiplication, and division, along with variable assignments
//! from 'a' to 'z'.
//!
//! ## Example
//! ```
//! # use syntree::{Root, Visitor, Calculator};
//!
//! let mut calculator = Calculator::default();
//! let root = Root::from_str("a 1 = b 2 3 * = a b +").unwrap();
//! let result = calculator.calc(&root);
//!
//! println!("Final result: {}", result); // prints 7
//! ```

use std::collections::HashMap;

use crate::parse_tree::*;

/// `Calculator` is a struct designed to evaluate parsed arithmetic expressions.
///
/// ## Usage
/// ```
/// # use syntree::{Calculator, Root};
/// # fn doc(root: Root) {
/// let mut calculator = Calculator::default();
/// let result = calculator.calc(&root);
/// println!("The result of the calculation is: {}", result);
/// # }
/// ```
#[derive(Default)]
pub struct Calculator{
	variables: HashMap<char, i64>,
}

impl Calculator {
    pub fn calc(&mut self, root: &Root) -> i64 {
        self.visit_root(root)
    }
}

impl Visitor for Calculator {
    fn visit_root(&mut self, r: &Root) -> i64 {
        let mut last_value = 0;
        for stmt in &r.stmt_list {
            last_value = self.visit_stmt(stmt);
        }
        last_value
    }

    fn visit_stmt(&mut self, s: &Stmt) -> i64 {
        match s {
            Stmt::Expr(expr) => self.visit_expr(expr),
            Stmt::Set(var, expr) => {
                let val = self.visit_expr(expr);
                self.variables.insert(*var, val);  // Store the value in the variable
                // val
				0
            },
        }
    }

    fn visit_expr(&mut self, e: &Expr) -> i64 {
        match e {
            Expr::Int(n) => *n,
            Expr::Var(v) => *self.variables.get(v).unwrap_or(&0),  // Retrieve the value, default to 0
            Expr::Add(lhs, rhs) => self.visit_expr(lhs) + self.visit_expr(rhs),
            Expr::Sub(lhs, rhs) => self.visit_expr(lhs) - self.visit_expr(rhs),
            Expr::Mul(lhs, rhs) => self.visit_expr(lhs) * self.visit_expr(rhs),
            Expr::Div(lhs, rhs) => {
                let divisor = self.visit_expr(rhs);
                if divisor != 0 {
                    self.visit_expr(lhs) / divisor
                } else {
                    panic!("attempt to divide by zero"); // Handle division by zero as needed
                }
            }
        }
    }
}



trait Visitor {
    fn visit_root(&mut self, r: &Root) -> i64;
    fn visit_stmt(&mut self, s: &Stmt) -> i64;
    fn visit_expr(&mut self, e: &Expr) -> i64;
}


// unit-tests

#[cfg(test)]
mod tests {
	use super::*;
	
	#[test]
	fn add() {
		let tree = Root::from_stmt(Stmt::add(4, 2));
		assert_eq!(Calculator::default().calc(&tree), 6);
	}
	
	#[test]
	fn sub() {
		let tree = Root::from_stmt(Stmt::sub(4, 2));
		assert_eq!(Calculator::default().calc(&tree), 2);
	}
	
	#[test]
	fn mul() {
		let tree = Root::from_stmt(Stmt::mul(4, 2));
		assert_eq!(Calculator::default().calc(&tree), 8);
	}
	
	#[test]
	fn div() {
		let tree = Root::from_stmt(Stmt::div(4, 2));
		assert_eq!(Calculator::default().calc(&tree), 2);
	}
	
	#[test]
	#[should_panic(expected = "attempt to divide by zero")]
	fn division_by_zero() {
		let tree = Root::from_stmt(Stmt::div(4, 0));
		Calculator::default().calc(&tree);
	}
	
	#[test]
	fn set() {
		let tree = Root::from_stmt(Stmt::set('a', 1));
		assert_eq!(Calculator::default().calc(&tree), 0);
	}
	
	#[test]
	fn vars() {
		let tree = Root {
			stmt_list: vec![
				Stmt::set('i', 1),
				Stmt::set('j', 2),
				Stmt::Expr(Expr::Add(
					Box::new(Expr::Var('i')),
					Box::new(Expr::Var('j')),
				)),
			],
		};
		assert_eq!(Calculator::default().calc(&tree), 3);
	}
}
