use c1::{analyze, interpret, parse};
use std::{env, fs, process::ExitCode};

fn main() -> ExitCode {
    let mut args = env::args();

    if args.len() < 2 {
        println!(
            "Usage: {} <c1-source>",
            args.next().as_deref().unwrap_or("c1")
        );
        return ExitCode::FAILURE;
    }

    // Read the source file into a string.
    let input = match fs::read_to_string(args.nth(1).unwrap()) {
        Ok(input) => input,
        Err(err) => {
            println!("failed to read c1 source file: {err}");
            return ExitCode::FAILURE;
        }
    };

    // Parse the source code into an AST.
    let mut ast = match parse(&input) {
        Ok(ast) => {
            println!("[✓] syntax");
            ast
        }
        Err(err) => {
            println!("[x] syntax");
            println!("{err}");
            return ExitCode::FAILURE;
        }
    };

    // Run semantic analysis on the AST, writing resolutions into the AST,
    // and collecting auxiliary information required for interpretation.
    let analysis = match analyze(&mut ast) {
        Ok(analysis) => {
            println!("[✓] analysis");
            analysis
        }
        Err(err) => {
            println!("[x] analysis");
            println!("{err}");
            return ExitCode::FAILURE;
        }
    };

    // Use the resolved AST and the auxiliary information from analysis
    // to execute the program in an interpreter.
    let output = match interpret(&ast, &analysis) {
        Ok(output) => {
            println!("[✓] execution");
            output
        }
        Err(err) => {
            println!("[x] execution");
            println!("{err}");
            return ExitCode::FAILURE;
        }
    };

    print!("{output}");

    ExitCode::SUCCESS
}
