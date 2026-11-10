//! `ckc`, the compiler's command-line driver (D96).

use std::process::ExitCode;

const USAGE: &str = "\
ckc — the Checkers compiler (usually run through `checkers`, the build tool)

USAGE:
    ckc run [--unverified] [--threads N] <FILE.ck> [ARG]...
                                               check and prove, then run `main` with ARGs
                                               (N worker threads, default: cores; 1 is deterministic)
    ckc build [--unverified] <FILE.ck> -o <PROGRAM>
                                               check and prove, then write an executable
                                               (its threads: CHECKERS_THREADS, default: cores)
    ckc trust <FILE.ck>                        print the trust ledger (what Z3, admits and checks vouch for)
    ckc check [--deny-warnings] <FILE.ck>...   type-check and run `check`s; report diagnostics
    ckc stage <FILE.ck>                        print the code staging generates (§8.9)
    ckc parse <FILE.ck>                        print the syntax tree
    ckc --version
";

fn main() -> ExitCode {
    // The elaborator recurses deeply, so everything runs on a big stack.
    let code = checkers::with_big_stack(|| {
        let args: Vec<String> = std::env::args().skip(1).collect();
        cli(&args)
    });
    ExitCode::from(code)
}

fn cli(args: &[String]) -> u8 {
    let code = match args.first().map(String::as_str) {
        Some("run") => return run(&args[1..]),
        Some("build") => return build(&args[1..]),
        Some("trust") => return trust(&args[1..]),
        Some("stage") => return stage(&args[1..]),
        Some("check") => check(&args[1..]),
        Some("parse") => parse(&args[1..]),
        Some("--version") | Some("-V") => {
            println!("ckc {}", env!("CARGO_PKG_VERSION"));
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

fn trust(args: &[String]) -> u8 {
    let [path] = args else {
        eprintln!("error: `trust` takes exactly one file\n\n{USAGE}");
        return 2;
    };
    let Ok(text) = read(path) else { return 2 };
    let c = checkers::check(path, &text);
    if c.errors() > 0 {
        eprint!("{}", c.report());
        return 1;
    }
    print!("{}", c.ledger);
    0
}

fn stage(args: &[String]) -> u8 {
    let [path] = args else {
        eprintln!("error: `stage` takes exactly one file\n\n{USAGE}");
        return 2;
    };
    let Ok(text) = read(path) else { return 2 };
    let c = checkers::check(path, &text);
    if c.errors() > 0 {
        eprint!("{}", c.report());
        return 1;
    }
    print!("{}", c.staged);
    0
}

fn run(args: &[String]) -> u8 {
    let mut unverified = false;
    let mut threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let mut args = args;
    loop {
        match args.first().map(String::as_str) {
            Some("--unverified") => {
                unverified = true;
                args = &args[1..];
            }
            Some("--threads") => {
                match args.get(1).and_then(|n| n.parse::<usize>().ok()).filter(|n| *n >= 1) {
                    Some(n) => threads = n,
                    None => {
                        eprintln!("error: `--threads` needs a number of threads, at least 1\n\n{USAGE}");
                        return 2;
                    }
                }
                args = &args[2..];
            }
            _ => break,
        }
    }
    let Some(path) = args.first() else {
        eprintln!("error: `run` needs a file\n\n{USAGE}");
        return 2;
    };
    let text = match read(path) {
        Ok(t) => t,
        Err(_) => return 2,
    };
    let ran = checkers::run(path, &text, &checkers::dir_of(path), &args[1..], unverified, threads);
    eprint!("{}", ran.report);
    ran.code
}

fn build(args: &[String]) -> u8 {
    let mut unverified = false;
    let mut out: Option<String> = None;
    let mut file: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--unverified" => unverified = true,
            "-o" => {
                i += 1;
                out = args.get(i).cloned();
            }
            f => file = Some(f.to_string()),
        }
        i += 1;
    }
    let (Some(path), Some(out)) = (file, out) else {
        eprintln!("error: `build` needs a file and `-o PROGRAM`\n\n{USAGE}");
        return 2;
    };
    let text = match read(&path) {
        Ok(t) => t,
        Err(_) => return 2,
    };
    let ran = checkers::build(&path, &text, &checkers::dir_of(&path), std::path::Path::new(&out), unverified);
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
