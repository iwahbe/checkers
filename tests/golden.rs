//! Golden tests (SPEC §12).
//!
//! tests/parse/NAME.ck  → NAME.out is the syntax tree, followed by any diagnostics.
//! tests/check/NAME.ck  → NAME.out is the parse + lint report.
//! tests/types/NAME.ck  → NAME.out is the full report (type checking included).
//! tests/run/NAME.args  → run the program named on its first line (SPEC §13.6);
//!                         NAME.out is its stdout, stderr and exit code.
//! examples/*.ck        → must check with no errors and no warnings.
//!
//! `UPDATE_GOLDEN=1 cargo test --test golden` rewrites the .out files.

use std::cell::RefCell;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;

fn files_with(dir: &Path, ext: &str) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == ext))
        .collect();
    v.sort();
    v
}

fn ck_files(dir: &Path) -> Vec<PathBuf> {
    files_with(dir, "ck")
}

/// A writer whose bytes the test can read afterwards.
#[derive(Clone, Default)]
struct Capture(Rc<RefCell<Vec<u8>>>);

impl Write for Capture {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(b);
        Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Run one `tests/run/NAME.args` case; the working directory is `tests/run`.
fn run_case(args_path: &Path) -> String {
    let spec = fs::read_to_string(args_path).unwrap();
    let mut lines = spec.lines();
    let program = lines.next().unwrap_or_default().to_string();
    let args: Vec<String> = lines.map(str::to_string).collect();
    let stdin = fs::read(args_path.with_extension("in")).unwrap_or_default();
    let text = fs::read_to_string(&program).unwrap_or_else(|e| panic!("{}: {program}: {e}", args_path.display()));
    let (out, err) = (Capture::default(), Capture::default());
    let io = checkers::run::Io {
        stdin: Box::new(std::io::Cursor::new(stdin)),
        stdout: Box::new(out.clone()),
        stderr: Box::new(err.clone()),
    };
    let name = Path::new(&program).file_name().unwrap().to_string_lossy().to_string();
    let ran = checkers::run(&name, &text, &args, io);
    let stdout = String::from_utf8_lossy(&out.0.borrow()).to_string();
    let stderr = ran.report.clone() + &String::from_utf8_lossy(&err.0.borrow());
    format!("-- stdout\n{stdout}-- stderr\n{stderr}-- exit {}\n", ran.code)
}

fn run(path: &Path, mode: &str) -> String {
    let text = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let c = if mode == "types" { checkers::check(&name, &text) } else { checkers::parse_only(&name, &text) };
    match mode {
        "parse" => {
            let mut out = checkers::syntax::print::module(&c.module);
            if !c.diags.is_empty() {
                out += "\n";
                out += &c.report();
            }
            out
        }
        _ => c.report(),
    }
}

fn main() {
    // `check` runs code (D40); the interpreter needs a big stack.
    checkers::run::with_big_stack(golden);
}

fn golden() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let mut failures = Vec::new();
    let mut count = 0;

    for mode in ["parse", "check", "types"] {
        for path in ck_files(&root.join("tests").join(mode)) {
            count += 1;
            let actual = run(&path, mode);
            let out_path = path.with_extension("out");
            let expected = fs::read_to_string(&out_path).unwrap_or_default();
            if actual != expected {
                if update {
                    fs::write(&out_path, &actual).unwrap();
                    println!("updated {}", out_path.strip_prefix(root).unwrap().display());
                } else {
                    failures.push(format!(
                        "── {} ──\n--- expected\n{expected}\n--- actual\n{actual}",
                        path.strip_prefix(root).unwrap().display()
                    ));
                }
            }
        }
    }

    let run_dir = root.join("tests").join("run");
    std::env::set_current_dir(&run_dir).unwrap();
    for path in files_with(&run_dir, "args") {
        count += 1;
        let actual = run_case(&path);
        let out_path = path.with_extension("out");
        let expected = fs::read_to_string(&out_path).unwrap_or_default();
        if actual != expected {
            if update {
                fs::write(&out_path, &actual).unwrap();
                println!("updated {}", out_path.strip_prefix(root).unwrap().display());
            } else {
                failures.push(format!(
                    "── {} ──\n--- expected\n{expected}\n--- actual\n{actual}",
                    path.strip_prefix(root).unwrap().display()
                ));
            }
        }
    }
    std::env::set_current_dir(root).unwrap();

    for path in ck_files(&root.join("examples")) {
        count += 1;
        let text = fs::read_to_string(&path).unwrap();
        let c = checkers::check(&path.file_name().unwrap().to_string_lossy(), &text);
        if !c.diags.is_empty() {
            failures.push(format!("── examples/{} must be clean ──\n{}", path.file_name().unwrap().to_string_lossy(), c.report()));
        }
    }

    if failures.is_empty() {
        println!("golden: {count} files ok");
    } else {
        for f in &failures {
            println!("{f}");
        }
        println!("golden: {} of {count} failed (UPDATE_GOLDEN=1 to accept)", failures.len());
        std::process::exit(1);
    }
}
