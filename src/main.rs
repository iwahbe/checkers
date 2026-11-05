//! `checkers` command-line driver.

use std::process::ExitCode;

const USAGE: &str = "\
checkers — the Checkers compiler (M0: front end)

USAGE:
    checkers check [--deny-warnings] <FILE.ck>...   parse and lint; report diagnostics
    checkers parse <FILE.ck>                        print the syntax tree
    checkers --version
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
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
    }
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
