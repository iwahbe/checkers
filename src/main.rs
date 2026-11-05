//! `checkers` command-line driver.

use std::process::ExitCode;

const USAGE: &str = "\
checkers — the Checkers compiler and interpreter

USAGE:
    checkers run <FILE.ck> [ARG]...                 type-check, then run `main` with ARGs
    checkers check [--deny-warnings] <FILE.ck>...   type-check and run `check`s; report diagnostics
    checkers parse <FILE.ck>                        print the syntax tree
    checkers --version
";

fn main() -> ExitCode {
    // The interpreter recurses for non-tail calls, so everything runs on a big stack.
    let code = checkers::run::with_big_stack(|| {
        let args: Vec<String> = std::env::args().skip(1).collect();
        cli(&args)
    });
    ExitCode::from(code)
}

fn cli(args: &[String]) -> u8 {
    let code = match args.first().map(String::as_str) {
        Some("run") => return run(&args[1..]),
        Some("check") => check(&args[1..]),
        Some("parse") => parse(&args[1..]),
        Some("--version") | Some("-V") => {
            println!("checkers {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some("--help") | Some("-h") | None => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("error: unknown command `{other}`\n\n{USAGE}");
            ExitCode::from(2)
        }
    };
    if code == ExitCode::SUCCESS {
        0
    } else if code == ExitCode::FAILURE {
        1
    } else {
        2
    }
}

fn run(args: &[String]) -> u8 {
    let Some(path) = args.first() else {
        eprintln!("error: `run` needs a file\n\n{USAGE}");
        return 2;
    };
    let text = match read(path) {
        Ok(t) => t,
        Err(_) => return 2,
    };
    let ran = checkers::run(path, &text, &args[1..], checkers::run::Io::process());
    eprint!("{}", ran.report);
    ran.code
}

fn read(path: &str) -> Result<String, ExitCode> {
    std::fs::read_to_string(path).map_err(|e| {
        eprintln!("error: cannot read `{path}`: {e}");
        ExitCode::from(2)
    })
}

fn check(args: &[String]) -> ExitCode {
    let deny = args.iter().any(|a| a == "--deny-warnings");
    let files: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    if files.is_empty() {
        eprintln!("error: no input files\n\n{USAGE}");
        return ExitCode::from(2);
    }
    let mut failed = false;
    for path in files {
        let text = match read(path) {
            Ok(t) => t,
            Err(c) => return c,
        };
        let c = checkers::check(path, &text);
        eprint!("{}", c.report());
        if c.errors() > 0 || (deny && c.warnings() > 0) {
            failed = true;
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn parse(args: &[String]) -> ExitCode {
    let [path] = args else {
        eprintln!("error: `parse` takes exactly one file\n\n{USAGE}");
        return ExitCode::from(2);
    };
    let text = match read(path) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let c = checkers::check(path, &text);
    print!("{}", checkers::syntax::print::module(&c.module));
    if !c.diags.is_empty() {
        eprint!("{}", c.report());
    }
    if c.errors() > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
