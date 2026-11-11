//! `ckc`, the compiler's command-line driver (D96).

use std::process::ExitCode;

const USAGE: &str = "\
ckc — the Checkers compiler (usually run through `checkers`, the build tool)

USAGE:
    ckc run [--unverified] [--threads N] <FILE.ck> [ARG]...
                                               check and prove, then run `main` with ARGs
                                               (N worker threads, default: cores; 1 is deterministic)
    ckc build [--unverified | --release] <FILE.ck> -o <PROGRAM>
                                               check and prove, then write an executable
                                               (its threads: CHECKERS_THREADS, default: cores);
                                               --release refuses any `admit` the program relies on
    ckc trust <FILE.ck>                        print the trust ledger (what Z3, admits and checks vouch for)
    ckc check [--deny-warnings] <FILE.ck>...   type-check and run `check`s; report diagnostics
    ckc check --json [--overlay MAP] <FILE.ck> the same as JSON lines, phase by phase, for tools (§15.5);
                                               MAP is a JSON object from paths to unsaved text
                                               (`-`: read it from standard input)

    check, run, build, trust and stage reuse Z3's answers from `.checkers/` beside the
    file (D100); --no-cache (before the file) or CHECKERS_NO_CACHE=1 turns that off.

    Before the file, packages (D111; `checkers` passes these from checkers.json):
      --package NAME=DIR    a dependency, importable as `NAME.module`
      --uses PKG=A,B        the packages PKG may import (`.` is this program's own)
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

static NO_CACHE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Cache Z3's answers beside `path`'s module root (D100), unless
/// `--no-cache` or `CHECKERS_NO_CACHE` says not to.
fn use_cache(path: &str) {
    let off = NO_CACHE.load(std::sync::atomic::Ordering::Relaxed) || std::env::var_os("CHECKERS_NO_CACHE").is_some();
    checkers::verify::set_cache((!off).then(|| checkers::dir_of(path).join(".checkers")));
}

fn cli(args: &[String]) -> u8 {
    // Options before the file (after it, arguments are the program's):
    // `--no-cache`, and the packages of this build (D111).
    let first_file = args.iter().position(|a| a.ends_with(".ck")).unwrap_or(args.len());
    let mut kept: Vec<String> = Vec::new();
    let mut pkgs = checkers::elab::stdlib::Packages::default();
    let mut uses: Vec<(String, Vec<String>)> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        if i < first_file && (a == "--package" || a == "--uses") {
            let Some(v) = args.get(i + 1).filter(|_| i + 1 < first_file) else {
                eprintln!("error: `{a}` needs a value: `{a} NAME=…`\n\n{USAGE}");
                return 2;
            };
            let Some((k, rest)) = v.split_once('=') else {
                eprintln!("error: `{a} {v}`: expected `NAME=…`");
                return 2;
            };
            if a == "--package" {
                let dir = std::path::Path::new(rest);
                if !dir.is_dir() {
                    eprintln!("error: `--package {v}`: no directory `{rest}`");
                    return 2;
                }
                if k == "std" || k == "." || k.is_empty() {
                    eprintln!("error: `--package {v}`: `{k}` can't name a package");
                    return 2;
                }
                pkgs.dirs.insert(k.to_string(), dir.to_path_buf());
            } else {
                let list = rest.split(',').filter(|x| !x.is_empty()).map(str::to_string).collect();
                uses.push((k.to_string(), list));
            }
            i += 2;
            continue;
        }
        if i < first_file && a == "--no-cache" {
            NO_CACHE.store(true, std::sync::atomic::Ordering::Relaxed);
        } else {
            kept.push(args[i].clone());
        }
        i += 1;
    }
    for (k, list) in uses {
        for n in list.iter().chain(std::iter::once(&k).filter(|k| *k != ".")) {
            if !pkgs.dirs.contains_key(n) {
                eprintln!("error: `--uses {k}=…` names `{n}`, which no `--package` gives");
                return 2;
            }
        }
        pkgs.uses.insert(k, list);
    }
    checkers::elab::stdlib::set_packages(pkgs);
    let args = kept;
    let args = &args[..];
    let needs_std = !matches!(args.first().map(String::as_str), None | Some("--version" | "--help" | "-h"));
    if needs_std {
        if let Err(e) = checkers::elab::stdlib::dir() {
            eprintln!("{e}");
            return 2;
        }
    }
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
    use_cache(path);
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
    use_cache(path);
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
    use_cache(path);
    let ran = checkers::run(path, &text, &checkers::dir_of(path), &args[1..], unverified, threads);
    eprint!("{}", ran.report);
    ran.code
}

fn build(args: &[String]) -> u8 {
    let mut unverified = false;
    let mut release = false;
    let mut out: Option<String> = None;
    let mut file: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--unverified" => unverified = true,
            "--release" => release = true,
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
    if release && unverified {
        eprintln!("error: `--release` builds only proven programs, so it can't be used with `--unverified`");
        return 2;
    }
    let text = match read(&path) {
        Ok(t) => t,
        Err(_) => return 2,
    };
    use_cache(&path);
    let ran = checkers::build(&path, &text, &checkers::dir_of(&path), std::path::Path::new(&out), unverified, release);
    eprint!("{}", ran.report);
    ran.code
}

fn read(path: &str) -> Result<String, ExitCode> {
    checkers::overlay::read(std::path::Path::new(path)).map_err(|e| {
        eprintln!("error: cannot read `{path}`: {e}");
        ExitCode::from(2)
    })
}

fn check(args: &[String]) -> ExitCode {
    let deny = args.iter().any(|a| a == "--deny-warnings");
    let json = args.iter().any(|a| a == "--json");
    // `--overlay FILE`: unsaved text for some paths (§15.5).
    let mut rest: Vec<&String> = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--overlay" {
            let Some(f) = it.next() else {
                eprintln!("error: `--overlay` needs a file\n\n{USAGE}");
                return ExitCode::from(2);
            };
            // `-`: standard input (a language server pipes it, §15.5).
            let text = if f == "-" {
                let mut t = String::new();
                std::io::Read::read_to_string(&mut std::io::stdin(), &mut t).map(|_| t)
            } else {
                std::fs::read_to_string(f)
            };
            let parsed = text.map_err(|e| e.to_string()).and_then(|t| checkers::json::string_object(&t));
            match parsed {
                Ok(m) => checkers::overlay::set(m),
                Err(e) => {
                    eprintln!("error: `--overlay {f}`: {e}");
                    return ExitCode::from(2);
                }
            }
        } else {
            rest.push(a);
        }
    }
    let files: Vec<&String> = rest.into_iter().filter(|a| !a.starts_with("--")).collect();
    if json {
        let [path] = files.as_slice() else {
            eprintln!("error: `check --json` takes exactly one file\n\n{USAGE}");
            return ExitCode::from(2);
        };
        let text = match read(path) {
            Ok(t) => t,
            Err(c) => return c,
        };
        use_cache(path);
        use std::io::Write;
        let stdout = std::io::stdout();
        let mut lock = stdout.lock();
        let failed = checkers::check_json(path, &text, &checkers::dir_of(path), &mut |line| {
            let _ = writeln!(lock, "{line}");
            let _ = lock.flush();
        });
        return if failed { ExitCode::FAILURE } else { ExitCode::SUCCESS };
    }
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
        use_cache(path);
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
