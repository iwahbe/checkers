//! The Checkers compiler. See SPEC.md for the language definition.
//!
//! Pipeline: lex (with layout) → parse → naming lints → elaborate and
//! type-check (with the embedded standard library) → termination and usage →
//! run `check`s (D40). `run` then erases and interprets the program (§13).

pub mod core;
pub mod diag;
pub mod elab;
pub mod lint;
pub mod run;
pub mod source;
pub mod stage;
pub mod syntax;
pub mod usage;
pub mod verify;

use diag::Diagnostic;
use std::io::Write as _;
use source::SourceFile;

/// Result of checking one file.
pub struct Checked {
    pub file: SourceFile,
    pub module: syntax::ast::Module,
    pub diags: Vec<Diagnostic>,
    /// Diagnostics in standard-library modules (compiler bugs), already rendered.
    pub internal: Vec<String>,
    /// Diagnostics in imported program modules (D53), with their files.
    pub others: Vec<(String, SourceFile, Vec<Diagnostic>)>,
    /// Proof obligations in this file, and how many the prover discharged.
    pub obligations: usize,
    pub proved: usize,
    /// The trust ledger (§7.4), rendered.
    pub ledger: String,
    /// Staged definitions (§8.9), for `checkers stage`.
    pub staged: String,
}

impl Checked {
    fn all_diags(&self) -> impl Iterator<Item = &Diagnostic> {
        self.others.iter().flat_map(|o| o.2.iter()).chain(self.diags.iter())
    }

    pub fn errors(&self) -> usize {
        self.all_diags().filter(|d| d.is_error()).count() + self.internal.len()
    }

    pub fn warnings(&self) -> usize {
        self.all_diags().filter(|d| !d.is_error()).count()
    }

    /// Diagnostics in source order (imported modules first), then a one-line summary.
    pub fn report(&self) -> String {
        let mut out = String::new();
        for (_, f, ds) in &self.others {
            if !ds.is_empty() {
                out += &diag::render_all(f, ds);
                out.push('\n');
            }
        }
        out += &diag::render_all(&self.file, &self.diags);
        for i in &self.internal {
            if !out.is_empty() {
                out.push('\n');
            }
            out += i;
        }
        if !out.is_empty() {
            out.push('\n');
        }
        out += &format!(
            "{}: {} error{}, {} warning{}",
            self.file.name,
            self.errors(),
            if self.errors() == 1 { "" } else { "s" },
            self.warnings(),
            if self.warnings() == 1 { "" } else { "s" },
        );
        if self.proved > 0 && self.errors() == 0 {
            out += &format!("; {} obligation{} proved", self.proved, if self.proved == 1 { "" } else { "s" });
        }
        out.push('\n');
        out
    }
}

/// Lex, parse and lint only.
pub fn parse_only(name: &str, text: &str) -> Checked {
    let file = SourceFile::new(name, text);
    let (module, mut diags) = syntax::parse_module(text);
    diags.extend(lint::naming(&module));
    Checked { file, module, diags, internal: Vec::new(), others: Vec::new(), obligations: 0, proved: 0, ledger: String::new(), staged: String::new() }
}

/// The directory `import a.b` looks in for `a/b.ck` (D53): the program's own.
fn dir_of(name: &str) -> std::path::PathBuf {
    std::path::Path::new(name).parent().map(|p| p.to_path_buf()).unwrap_or_default()
}

/// Run every implemented phase over one source file, including its `check`s
/// and proofs, and those of every module it imports.
pub fn check(name: &str, text: &str) -> Checked {
    check_in(name, text, &dir_of(name))
}

/// `check`, with imported modules looked up in `dir`.
pub fn check_in(name: &str, text: &str, dir: &std::path::Path) -> Checked {
    let (mut c, e) = elaborate(name, text, dir);
    if let Some((e, user)) = &e {
        run_checks(&mut c, e, user);
        prove(&mut c, e, user);
        stage_module(&mut c, e, user);
    }
    c
}

/// Stage the module's functions that call compile-time functions (§8.9),
/// reporting where compile-time evaluation fails.
fn stage_module(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    for (k, info) in e.g.defs.iter().enumerate() {
        if *info.module != *user || !info.comptime.is_empty() {
            continue;
        }
        let Some(body) = &info.body else { continue };
        if !stage::needs_staging(&e.g, body) {
            continue;
        }
        match stage::stage(&e.g, body) {
            Ok(t) => {
                c.staged += &stage::show_def(&e.g, &info.name, &t);
                c.staged += "\n";
            }
            Err(why) => {
                let span = e.fn_meta.get(&core::DefId(k as u32)).map(|m| m.span).unwrap_or_default();
                let d = diag::Diagnostic::error("E0273", format!("compile-time evaluation failed in `{}`", info.name), span)
                    .with_note(why);
                route(c, e, user, user, d);
            }
        }
    }
}

/// Check and prove the standard library itself (its lemmas and postconditions).
/// Returns the rendered errors; empty when it all verifies.
pub fn check_stdlib() -> String {
    let mut e = elab::Elab::new();
    for (m, _) in elab::stdlib::MODULES {
        e.load_stdlib(m);
    }
    let mut out = String::new();
    for (m, d) in &e.diags {
        if let Some(f) = e.sources.get(m) {
            out += &d.render(f);
        }
    }
    if !out.is_empty() {
        return out;
    }
    for (m, _) in elab::stdlib::MODULES {
        let v = verify::verify(&e, m);
        if let Some(f) = e.sources.get(*m) {
            out += &diag::render_all(f, &v.diags);
        }
    }
    out
}

/// The modules whose code is checked: imported program modules, then this one.
fn program_modules(e: &elab::Elab, user: &str) -> Vec<String> {
    let mut v = e.user_modules.clone();
    v.push(user.to_string());
    v
}

/// File a diagnostic of module `m` where it belongs.
fn route(c: &mut Checked, e: &elab::Elab, user: &str, m: &str, d: Diagnostic) {
    if m == user {
        c.diags.push(d);
    } else if e.user_modules.iter().any(|u| u == m) {
        match c.others.iter_mut().find(|o| o.0 == m) {
            Some(o) => o.2.push(d),
            None => {
                let f = e.sources.get(m).map(|f| SourceFile::new(f.name.clone(), f.text.clone())).unwrap_or_else(|| SourceFile::new(m, ""));
                c.others.push((m.to_string(), f, vec![d]));
            }
        }
    } else {
        let rendered = match e.sources.get(m) {
            Some(f) => d.render(f),
            None => format!("{}: {}\n", m, d.message),
        };
        c.internal.push(format!("internal error (standard library module `{m}`):\n{rendered}"));
    }
}

/// Discharge the proof obligations (§7.2) once everything else is clean.
fn prove(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    let mut ledger = String::new();
    for m in program_modules(e, user) {
        let v = verify::verify(e, &m);
        c.proved += v.proved;
        if let Some(f) = e.sources.get(&m) {
            ledger += &verify::ledger_text(f, &v);
        }
        for d in v.diags {
            route(c, e, user, &m, d);
        }
    }
    // One solver line at the end.
    let solver: Vec<&str> = ledger.lines().filter(|l| l.starts_with("solver: ")).collect();
    let last = solver.last().map(|s| s.to_string());
    let mut out: String = ledger.lines().filter(|l| !l.starts_with("solver: ")).map(|l| format!("{l}\n")).collect();
    if let Some(s) = last {
        out += &s;
        out.push('\n');
    }
    c.ledger = out;
}

/// Parse, lint and type-check; also returns the elaborator and the module name.
fn elaborate(name: &str, text: &str, dir: &std::path::Path) -> (Checked, Option<(elab::Elab, String)>) {
    let mut c = parse_only(name, text);
    if c.diags.iter().any(|d| d.is_error()) {
        return (c, None); // type checking a broken parse only produces noise
    }
    let stem = std::path::Path::new(name).file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let e = elab::check_module(&stem, &c.file, &c.module, Some(dir));
    let user = c.module.name.as_ref().map(|q| q.dotted()).unwrap_or(stem);
    for (m, d) in &e.diags {
        route(&mut c, &e, &user, m, d.clone());
    }
    c.obligations = e.obligations.iter().filter(|o| o.module == user).count();
    (c, Some((e, user)))
}

fn quiet_io() -> run::Io {
    run::Io { stdin: Box::new(std::io::empty()), stdout: Box::new(std::io::sink()), stderr: Box::new(std::io::sink()) }
}

/// Evaluate the module's `check` declarations (D40).
fn run_checks(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    let mut it = run::Interp::new(&e.g, quiet_io());
    let mods = program_modules(e, user);
    for (m, span, t) in &e.checks {
        if !mods.contains(m) {
            continue;
        }
        match it.eval_closed(t) {
            Ok(v) if it.is_false(&v) => {
                let mut d = diag::Diagnostic::error("E0260", "this `check` is false", *span).with_label("evaluates to `False`");
                if let core::Tm::PrimApp(core::Prim::Eq, sides) = t {
                    if let [l, r] = sides.as_slice() {
                        if let (Ok(lv), Ok(rv)) = (it.eval_closed(l), it.eval_closed(r)) {
                            d = d
                                .with_note(format!("left side:  `{}`", run::value::show(&e.g, &lv, 0)))
                                .with_note(format!("right side: `{}`", run::value::show(&e.g, &rv, 0)));
                        }
                    }
                }
                route(c, e, user, m, d);
            }
            Ok(_) => {}
            Err(err) => route(
                c,
                e,
                user,
                m,
                diag::Diagnostic::error("E0261", "this `check` stopped with a runtime error", *span)
                    .with_label("evaluating this failed")
                    .with_note(err.to_string()),
            ),
        }
    }
}

/// The outcome of `run`.
pub struct Ran {
    /// Diagnostics (empty when there are none).
    pub report: String,
    /// Process exit code: the program's, 2 if it didn't type-check, 70 after a runtime error.
    pub code: u8,
}

/// Proof failures (D48): the only errors `run --unverified` tolerates.
fn is_proof_failure(d: &Diagnostic) -> bool {
    matches!(d.code, "E0450" | "E0451" | "E0452")
}

/// Check `text`, then call its exported `main` with `args` (D43, §13.4).
/// With `unverified`, a program whose only errors are unproven obligations
/// runs anyway, with the runtime checks of §13.3 (D48).
pub fn run(name: &str, text: &str, args: &[String], io: run::Io, unverified: bool) -> Ran {
    run_in(name, text, &dir_of(name), args, io, unverified)
}

/// `run`, with imported modules looked up in `dir`.
pub fn run_in(name: &str, text: &str, dir: &std::path::Path, args: &[String], io: run::Io, unverified: bool) -> Ran {
    let (mut c, e) = elaborate(name, text, dir);
    let Some((e, user)) = e else { return Ran { report: c.report(), code: 2 } };
    run_checks(&mut c, &e, &user);
    prove(&mut c, &e, &user);
    let mut report = if c.all_diags().next().is_none() && c.internal.is_empty() { String::new() } else { c.report() };
    let blocking = c.internal.len() + c.all_diags().filter(|d| d.is_error() && !(unverified && is_proof_failure(d))).count();
    if blocking > 0 {
        return Ran { report, code: 2 };
    }
    if c.errors() > 0 {
        report += &format!("running with {} unproven obligation(s) (--unverified)\n", c.errors());
    }
    let exported = e.modules.get(&user).is_some_and(|m| m.exported_values.contains("main"));
    let main = e.g.defs.iter().position(|d| *d.module == user && &*d.name == "main");
    let (Some(main), true) = (main, exported) else {
        return Ran { report: format!("{report}error: `{}` has no exported `main` function\n", c.file.name), code: 2 };
    };
    let mut it = run::Interp::new(&e.g, io);
    let code = match it.run_main(core::DefId(main as u32), args) {
        Ok(code) => code,
        Err(err) => {
            let _ = std::io::Write::flush(&mut it.io.stdout);
            let _ = writeln!(it.io.stderr, "{err}");
            70
        }
    };
    it.flush();
    Ran { report, code }
}
