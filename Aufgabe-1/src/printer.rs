//! This module provides a [`Printer`] struct that implements the [`Visitor`]
//! trait to format and print parse trees represented by the [`Root`], [`Stmt`],
//! and [`Expr`] types.
//!
//! ## Functionality
//!
//! The `Printer` is designed to convert parsed expressions and statements into
//! a human-readable string format. It constructs a formatted string by visiting
//! each node in the parse tree and producing an appropriate string
//! representation, including handling nested expressions and variable
//! assignments.
//!
//! ## Usage
//!
//! Create an instance of `Printer`, then use it to format a parse tree by
//! passing a `Root` object to the `format` method. The method will visit each
//! node in the tree and accumulate the formatted output.
//!
//! ## Examples
//!
//! Basic usage:
//! ```
//! # use syntree::{Root, Printer};
//! let root = Root::from_str("a 3 5 + =").unwrap();
//! let mut printer = Printer::default();
//! let output = printer.format(&root);
//!
//! println!("{}", output); // prints a=(3+5)
//! ```

use crate::parse_tree::*;

/// `Printer` is a struct used for formatting parse trees into human-readable
/// strings.
///
/// ## Example
/// ```
/// # use syntree::{Root, Printer};
/// # fn doc(root: Root) {
/// let mut printer = Printer::default();
/// let formatted_output = printer.format(&root);
/// println!("{}", formatted_output);
/// # }
/// ```
#[derive(Default)]
pub struct Printer {
    output: String,
}

impl Printer {
    pub fn format(&mut self, root: &Root) -> String {
        self.visit_root(root)
    }
}

impl Visitor for Printer {
    fn visit_root(&mut self, r: &Root) -> String {
        self.output.clear();  // Ensure the output starts empty

        let statements: Vec<String> = r.stmt_list.iter()
            .map(|stmt| self.visit_stmt(stmt))  // Collect the formatted statements
            .collect();

        self.output = statements.join("\n");  // Join all statements with new lines
        self.output.clone()  // Return the output
    }

    fn visit_stmt(&mut self, s: &Stmt) -> String {
        match s {
            Stmt::Expr(expr) => self.visit_expr(expr),
            Stmt::Set(var, expr) => format!("{}={}", var, self.visit_expr(expr)),
        }
    }

    fn visit_expr(&mut self, e: &Expr) -> String {
        match e {
            Expr::Int(n) => n.to_string(),
            Expr::Var(v) => v.to_string(),
            Expr::Add(lhs, rhs) => format!("({}+{})", self.visit_expr(lhs), self.visit_expr(rhs)),
            Expr::Sub(lhs, rhs) => format!("({}-{})", self.visit_expr(lhs), self.visit_expr(rhs)),
            Expr::Mul(lhs, rhs) => format!("({}*{})", self.visit_expr(lhs), self.visit_expr(rhs)),
            Expr::Div(lhs, rhs) => format!("({}/{})", self.visit_expr(lhs), self.visit_expr(rhs)),
        }
    }
}


trait Visitor {
    fn visit_root(&mut self, r: &Root) -> String;
    fn visit_stmt(&mut self, s: &Stmt) -> String;
    fn visit_expr(&mut self, e: &Expr) -> String;
}


// unit-tests

#[cfg(test)]
mod tests {
	use super::*;
	
	#[test]
	fn add() {
		let tree = Root::from_stmt(Stmt::add(4,2));
		assert_eq!(Printer::default().format(&tree), "(4+2)");
	}
	
	#[test]
	fn sub() {
		let tree = Root::from_stmt(Stmt::sub(4,2));
		assert_eq!(Printer::default().format(&tree), "(4-2)");
	}
	
	#[test]
	fn mul() {
		let tree = Root::from_stmt(Stmt::mul(4,2));
		assert_eq!(Printer::default().format(&tree), "(4*2)");
	}
	
	#[test]
	fn div() {
		let tree = Root::from_stmt(Stmt::div(4,2));
		assert_eq!(Printer::default().format(&tree), "(4/2)");
	}
	
	#[test]
	fn set() {
		let tree = Root::from_stmt(Stmt::set('a',1));
		assert_eq!(Printer::default().format(&tree), "a=1");
	}
}
