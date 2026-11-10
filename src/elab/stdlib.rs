//! The standard library: the package `std`, read from disk (D104).
//!
//! `ckc` finds it through `CHECKERS_STD`, else `../lib/checkers/std` from
//! its own directory (an installation), else the `stdlib/` of the source
//! tree it was built from (builds from the source tree; a release build
//! sets `CHECKERS_RELEASE` at compile time to leave this out). Module
//! `std.a.b` is the file `a/b.ck` there.

use super::Elab;
use crate::diag::Diagnostic;
use crate::source::SourceFile;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};

/// The places looked in, in order.
fn candidates() -> Vec<PathBuf> {
    let mut out = Vec::new();
    if let Some(d) = std::env::var_os("CHECKERS_STD") {
        out.push(PathBuf::from(d));
        return out;
    }
    if let Some(dir) = std::env::current_exe().ok().and_then(|e| e.parent().map(|p| p.to_path_buf())) {
        out.push(dir.join("..").join("lib").join("checkers").join("std"));
    }
    if option_env!("CHECKERS_RELEASE").is_none() {
        out.push(PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/stdlib")));
    }
    out
}

/// The standard library's directory, or why there is none.
pub fn dir() -> Result<PathBuf, String> {
    static DIR: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    DIR.get_or_init(|| {
        let cs = candidates();
        cs.iter().find(|d| d.join("prelude.ck").is_file()).cloned().ok_or_else(|| {
            let looked: Vec<String> = cs.iter().map(|d| format!("  {}", d.display())).collect();
            format!(
                "error: the standard library was not found; looked in:\n{}\nhelp: set CHECKERS_STD to the directory holding prelude.ck",
                looked.join("\n")
            )
        })
    })
    .clone()
}

/// The text of standard-library module `name` (`std.list`), read once.
pub fn source(name: &str) -> Option<String> {
    static TEXTS: OnceLock<Mutex<HashMap<String, Option<String>>>> = OnceLock::new();
    let rest = name.strip_prefix("std.")?;
    let texts = TEXTS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut t = texts.lock().unwrap_or_else(|e| e.into_inner());
    t.entry(name.to_string())
        .or_insert_with(|| {
            let d = dir().ok()?;
            let rel: PathBuf = rest.split('.').collect::<PathBuf>().with_extension("ck");
            std::fs::read_to_string(d.join(rel)).ok()
        })
        .clone()
}

/// Every standard-library module, sorted by name.
pub fn modules() -> Vec<String> {
    fn walk(base: &std::path::Path, d: &std::path::Path, out: &mut Vec<String>) {
        let Ok(rd) = std::fs::read_dir(d) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(base, &p, out);
            } else if p.extension().is_some_and(|x| x == "ck") {
                if let Ok(rel) = p.strip_prefix(base) {
                    let name: Vec<String> = rel.with_extension("").iter().map(|c| c.to_string_lossy().to_string()).collect();
                    out.push(format!("std.{}", name.join(".")));
                }
            }
        }
    }
    let mut out = Vec::new();
    if let Ok(d) = dir() {
        walk(&d, &d, &mut out);
    }
    out.sort();
    out
}

impl Elab {
    /// Load a stdlib module if it isn't loaded yet. Returns false if it doesn't exist.
    pub fn load_stdlib(&mut self, name: &str) -> bool {
        if self.modules.contains_key(name) {
            return true;
        }
        let Some(text) = source(name) else { return false };
        let rel = name.trim_start_matches("std.").replace('.', "/");
        let file = SourceFile::new(format!("<std>/{rel}.ck"), text.clone());
        let (m, diags) = crate::syntax::parse_module(&text);
        for d in diags {
            self.diags.push((name.to_string(), d));
        }
        self.sources.insert(name.to_string(), file);
        self.require_declared(name, &m);
        let saved = std::mem::take(&mut self.cur);
        let saved_fn = self.cur_fn.take();
        let saved_calls = std::mem::take(&mut self.calls);
        let saved_mod_fns = std::mem::take(&mut self.module_fns);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.elab_module(name, &m, true);
        self.cur = saved;
        self.cur_fn = saved_fn;
        self.calls = saved_calls;
        self.module_fns = saved_mod_fns;
        self.deferred = saved_deferred;
        true
    }

    /// E0223 unless the file imported as `name` declares `module name`.
    fn require_declared(&mut self, name: &str, m: &crate::syntax::ast::Module) {
        match &m.name {
            Some(q) if q.dotted() == name => {}
            other => {
                let span = other.as_ref().map(|q| q.span).unwrap_or_default();
                let found = other.as_ref().map(|q| q.dotted()).unwrap_or_default();
                self.diags.push((
                    name.to_string(),
                    Diagnostic::error("E0223", format!("this file must declare `module {name}`, because it is imported as `{name}`"), span)
                        .with_label(if found.is_empty() { "no module declaration".to_string() } else { format!("declares `{found}`") })
                        .with_help(format!("start the file with `module {name}`")),
                ));
            }
        }
    }

    /// Load the program module `a.b` from `a/b.ck` beside the program (D53).
    /// Returns false if there is no such file.
    pub fn load_user(&mut self, name: &str, _span: crate::source::Span) -> bool {
        let Some(base) = self.base_dir.clone() else { return false };
        let rel: std::path::PathBuf = name.split('.').collect::<std::path::PathBuf>().with_extension("ck");
        let path = base.join(&rel);
        let Ok(text) = std::fs::read_to_string(&path) else { return false };
        let file = SourceFile::new(path.to_string_lossy().to_string(), text.clone());
        let (m, diags) = crate::syntax::parse_module(&text);
        let broken = diags.iter().any(|d| d.is_error());
        for d in diags {
            self.diags.push((name.to_string(), d));
        }
        for d in crate::lint::naming(&m) {
            self.diags.push((name.to_string(), d));
        }
        self.sources.insert(name.to_string(), file);
        self.user_modules.push(name.to_string());
        if broken {
            // Its errors are reported; importers see an empty module.
            self.modules.insert(name.to_string(), super::ModuleInfo { name: name.to_string(), ..Default::default() });
            return true;
        }
        self.require_declared(name, &m);
        let saved = std::mem::take(&mut self.cur);
        let saved_fn = self.cur_fn.take();
        let saved_calls = std::mem::take(&mut self.calls);
        let saved_mod_fns = std::mem::take(&mut self.module_fns);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.elab_module(name, &m, false);
        self.cur = saved;
        self.cur_fn = saved_fn;
        self.calls = saved_calls;
        self.module_fns = saved_mod_fns;
        self.deferred = saved_deferred;
        true
    }

    pub fn stdlib_error(&mut self, name: &str, d: Diagnostic) {
        self.diags.push((name.to_string(), d));
    }
}
