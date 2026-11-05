//! Golden tests (SPEC §12).
//!
//! tests/parse/NAME.ck  → NAME.out is the syntax tree, followed by any diagnostics.
//! tests/check/NAME.ck  → NAME.out is the parse + lint report.
//! tests/types/NAME.ck  → NAME.out is the full report (type checking included).
//! examples/*.ck        → must check with no errors and no warnings.
//!
//! `UPDATE_GOLDEN=1 cargo test --test golden` rewrites the .out files.

use std::fs;
use std::path::{Path, PathBuf};

fn ck_files(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "ck"))
        .collect();
    v.sort();
    v
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
