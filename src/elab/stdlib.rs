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

/// The packages of this build (D109, D111): set once from `ckc`'s
/// `--package` and `--uses` flags.
#[derive(Default, Clone, Debug)]
pub struct Packages {
    /// Each dependency's directory.
    pub dirs: HashMap<String, PathBuf>,
    /// The packages each package may import; `.` is the program's own.
    pub uses: HashMap<String, Vec<String>>,
}

static PACKAGES: OnceLock<Packages> = OnceLock::new();

/// Set this build's packages (once, before checking).
pub fn set_packages(p: Packages) {
    let _ = PACKAGES.set(p);
}

pub fn packages() -> &'static Packages {
    PACKAGES.get_or_init(Packages::default)
}

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
            crate::overlay::read(&d.join(rel)).ok()
        })
        .clone()
}

/// Whether `path` is the file of standard-library module `name`.
pub fn is_std_file(name: &str, path: &std::path::Path) -> bool {
    let Some(rest) = name.strip_prefix("std.") else { return false };
    let Ok(d) = dir() else { return false };
    let own = d.join(rest.split('.').collect::<PathBuf>().with_extension("ck"));
    let same = |p: &std::path::Path| std::fs::canonicalize(p).unwrap_or_else(|_| crate::overlay::absolute(p));
    same(&own) == same(path)
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
        if let Ok(d) = dir() {
            self.paths.insert(name.to_string(), crate::overlay::absolute(&d.join(format!("{rel}.ck"))));
        }
        let (m, diags) = crate::syntax::parse_module(&text);
        for d in diags {
            self.diags.push((name.to_string(), d));
        }
        self.sources.insert(name.to_string(), file);
        self.require_declared(name, name, &m);
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

    /// E0223 unless the file of module `key` declares `module name`.
    fn require_declared(&mut self, key: &str, name: &str, m: &crate::syntax::ast::Module) {
        match &m.name {
            Some(q) if q.dotted() == name => {}
            other => {
                let span = other.as_ref().map(|q| q.span).unwrap_or_default();
                let found = other.as_ref().map(|q| q.dotted()).unwrap_or_default();
                let why = if key == name {
                    format!("because it is imported as `{name}`")
                } else {
                    let pkg = key.strip_suffix(name).unwrap_or(key).trim_end_matches('.');
                    format!("its path in package `{pkg}`")
                };
                self.diags.push((
                    key.to_string(),
                    Diagnostic::error("E0223", format!("this file must declare `module {name}`, {why}"), span)
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
        self.load_file(name, name, &base, None)
    }

    /// Load module `rel` of dependency `pkg` (D111): the file `rel`'s path
    /// in the package's directory, known as `pkg.rel`.
    pub fn load_package(&mut self, pkg: &str, rel: &str) -> bool {
        let Some(base) = packages().dirs.get(pkg).cloned() else { return false };
        self.load_file(&format!("{pkg}.{rel}"), rel, &base, Some(pkg))
    }

    /// Load the module known as `key`, declared `module declared`, from
    /// `declared`'s path under `base`.
    fn load_file(&mut self, key: &str, declared: &str, base: &std::path::Path, pkg: Option<&str>) -> bool {
        let rel: PathBuf = declared.split('.').collect::<PathBuf>().with_extension("ck");
        let path = base.join(&rel);
        let Ok(text) = crate::overlay::read(&path) else { return false };
        self.paths.insert(key.to_string(), crate::overlay::absolute(&path));
        let shown = match pkg {
            Some(p) => format!("<{p}>/{}", rel.to_string_lossy()),
            None => path.to_string_lossy().to_string(),
        };
        let file = SourceFile::new(shown, text.clone());
        let (m, diags) = crate::syntax::parse_module(&text);
        let broken = diags.iter().any(|d| d.is_error());
        for d in diags {
            self.diags.push((key.to_string(), d));
        }
        for d in crate::lint::naming(&m) {
            self.diags.push((key.to_string(), d));
        }
        self.sources.insert(key.to_string(), file);
        self.user_modules.push(key.to_string());
        if let Some(p) = pkg {
            self.module_pkg.insert(key.to_string(), p.to_string());
        }
        if broken {
            // Its errors are reported; importers see an empty module.
            self.modules.insert(key.to_string(), super::ModuleInfo { name: key.to_string(), ..Default::default() });
            return true;
        }
        self.require_declared(key, declared, &m);
        let saved = std::mem::take(&mut self.cur);
        let saved_fn = self.cur_fn.take();
        let saved_calls = std::mem::take(&mut self.calls);
        let saved_mod_fns = std::mem::take(&mut self.module_fns);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.elab_module(key, &m, false);
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
