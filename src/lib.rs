//! The Checkers compiler. See SPEC.md for the language definition.
//!
//! Pipeline: lex (with layout) → parse → naming lints → elaborate and
//! type-check (with the embedded standard library) → termination and usage →
//! run `check`s (D40). `run` then erases and interprets the program (§13).

pub mod core;
pub mod diag;
pub mod elab;
pub mod lint;
pub mod native;
pub mod source;
pub mod stage;
pub mod syntax;
pub mod usage;
pub mod verify;

use diag::Diagnostic;
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
        // Each module's diagnostics, a blank line between them and before the summary.
        let mut parts: Vec<String> = Vec::new();
        for (_, f, ds) in &self.others {
            if !ds.is_empty() {
                parts.push(diag::render_all(f, ds));
            }
        }
        if !self.diags.is_empty() {
            parts.push(diag::render_all(&self.file, &self.diags));
        }
        parts.extend(self.internal.iter().cloned());
        let mut out = parts.join("\n");
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
pub fn dir_of(name: &str) -> std::path::PathBuf {
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

/// Stage the program (§8.9): report where compile-time evaluation fails, and
/// keep the module's staged code for `checkers stage`.
fn stage_module(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    let (staged, errs) = stage::stage_program(&e.g);
    for (d, why) in errs {
        let info = &e.g.defs[d.0 as usize];
        if *info.module != *user {
            continue;
        }
        let span = e.fn_meta.get(&d).map(|m| m.span).unwrap_or_default();
        let dg = diag::Diagnostic::error("E0273", format!("compile-time evaluation failed in `{}`", info.name), span).with_note(why);
        route(c, e, user, user, dg);
    }
    let names: Vec<String> = staged.extra.iter().map(|x| x.0.clone()).collect();
    for (k, info) in e.g.defs.iter().enumerate() {
        if let (true, Some(t)) = (*info.module == *user, staged.bodies.get(&core::DefId(k as u32))) {
            c.staged += &stage::show_def(&e.g, &info.name, t, &names);
            c.staged += "\n";
        }
    }
    for (name, t) in &staged.extra {
        c.staged += &stage::show_def(&e.g, name, t, &names);
        c.staged += "\n";
    }
    trusted_builtins(c, e, user, &staged);
}

/// Add the builtins the program relies on to the trust ledger: those reachable
/// from `main`, or from every function of the program if it has none (§16.3).
fn trusted_builtins(c: &mut Checked, e: &elab::Elab, user: &str, staged: &stage::Staged) {
    let mut progs: Vec<String> = e.user_modules.iter().filter(|m| e.package_of(m) == ".").cloned().collect();
    progs.push(user.to_string());
    let main = e.g.defs.iter().position(|d| *d.module == *user && &*d.name == "main");
    let roots: Vec<u32> = match main {
        Some(m) => vec![m as u32],
        None => (0..e.g.defs.len() as u32)
            .filter(|d| progs.iter().any(|m| **m == *e.g.defs[*d as usize].module) && e.fn_meta.contains_key(&core::DefId(*d)))
            .collect(),
    };
    let mut p = native::lower::Program::new(&e.g, Some(staged));
    native::lower::Lowerer::new(&e.g, Some(staged), &mut p).add_defs(&roots);
    let mut lines: Vec<(String, String)> = Vec::new();
    for (d, shape) in &p.defs {
        if !matches!(shape, native::lower::DefShape::Builtin { .. }) {
            continue;
        }
        let info = &e.g.defs[*d as usize];
        let at = match (e.sources.get(&*info.module), e.fn_meta.get(&core::DefId(*d))) {
            (Some(f), Some(m)) => {
                let (line, col) = f.line_col(m.span.start);
                format!("{}:{line}:{col}", f.name)
            }
            _ => info.module.to_string(),
        };
        let full = format!("{}.{}", info.module, info.name);
        lines.push((full.clone(), format!("{at}  {:<8} {full}\n", "builtin")));
    }
    lines.sort();
    let text: String = lines.into_iter().map(|l| l.1).collect();
    // Before the solver line.
    let k = c.ledger.find("solver: ").unwrap_or(c.ledger.len());
    c.ledger.insert_str(k, &text);
}

/// Check and prove the standard library itself (its lemmas and postconditions).
/// Returns the rendered errors; empty when it all verifies.
pub fn check_stdlib() -> String {
    let mut e = elab::Elab::new();
    let modules = elab::stdlib::modules();
    for m in &modules {
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
    for m in &modules {
        let v = verify::verify(&e, m);
        if let Some(f) = e.sources.get(m) {
            out += &diag::render_all(f, &v.diags);
        }
    }
    out
}

/// The modules whose code is checked: the standard-library modules the
/// program loads and its dependencies' (D109), sorted; then its own imported
/// modules, and this one.
fn program_modules(e: &elab::Elab, user: &str) -> Vec<String> {
    let mut v = std_modules(e);
    let mut deps: Vec<String> = e.user_modules.iter().filter(|m| e.package_of(m) != ".").cloned().collect();
    deps.sort();
    v.extend(deps);
    v.extend(e.user_modules.iter().filter(|m| e.package_of(m) == ".").cloned());
    v.push(user.to_string());
    v
}

/// The standard-library modules loaded, sorted.
fn std_modules(e: &elab::Elab) -> Vec<String> {
    let mut v: Vec<String> = e.modules.keys().filter(|m| m.starts_with("std.")).cloned().collect();
    v.sort();
    v
}

/// File a diagnostic of module `m` where it belongs.
fn route(c: &mut Checked, e: &elab::Elab, user: &str, m: &str, d: Diagnostic) {
    if m == user {
        c.diags.push(d);
    } else if e.sources.contains_key(m) {
        // Imported program modules and standard-library modules alike (D104).
        match c.others.iter_mut().find(|o| o.0 == m) {
            Some(o) => o.2.push(d),
            None => {
                let f = e.sources.get(m).map(|f| SourceFile::new(f.name.clone(), f.text.clone())).unwrap_or_else(|| SourceFile::new(m, ""));
                c.others.push((m.to_string(), f, vec![d]));
            }
        }
    } else {
        c.internal.push(format!("internal error (module `{m}`, which has no source): {}\n", d.message));
    }
}

/// Discharge the proof obligations (§7.2) once everything else is clean.
fn prove(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    let mut ledger = String::new();
    let (mut asked, mut reused) = (0, 0);
    for m in program_modules(e, user) {
        let v = verify::verify(e, &m);
        // The standard library and dependencies are summarized (D110, D111).
        let own = e.package_of(&m) == ".";
        if own {
            c.proved += v.proved;
        }
        asked += v.asked;
        reused += v.reused;
        if let Some(f) = e.sources.get(&m) {
            ledger += &if own { verify::ledger_text(f, &v) } else { verify::ledger_summary(f, &v) };
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
    if reused > 0 {
        out += &format!("cache: {reused} of {asked} Z3 answers reused (D100)\n");
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

/// Evaluate the module's `check` declarations (D40).
fn run_checks(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    let mods = program_modules(e, user);
    if !e.checks.iter().any(|(m, _, _)| mods.contains(m)) {
        return;
    }
    // Native code (D80): one in-memory module for all of this program's checks.
    let mut ev = native::eval::Evaluator::new(&e.g);
    for (m, span, t) in &e.checks {
        if !mods.contains(m) {
            continue;
        }
        match ev.eval(t) {
            Ok(v) if ev.is_false(v) => {
                let mut d = diag::Diagnostic::error("E0260", "this `check` is false", *span).with_label("evaluates to `False`");
                if let core::Tm::PrimApp(core::Prim::Eq, sides) = t {
                    if let [l, r] = sides.as_slice() {
                        if let (Ok(lv), Ok(rv)) = (ev.eval(l), ev.eval(r)) {
                            d = d
                                .with_note(format!("left side:  `{}`", ev.show(lv)))
                                .with_note(format!("right side: `{}`", ev.show(rv)));
                            ev.release(lv);
                            ev.release(rv);
                        }
                    }
                }
                route(c, e, user, m, d);
            }
            Ok(v) => ev.release(v),
            Err(err) => route(
                c,
                e,
                user,
                m,
                diag::Diagnostic::error("E0261", "this `check` stopped with a runtime error", *span)
                    .with_label("evaluating this failed")
                    .with_note(err),
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

/// Check and prove `text`, then call its exported `main` with `args` (D43,
/// §13.4), as native code (§14). The program writes to this process's
/// standard streams, so the report is printed to standard error before it
/// runs; the returned report is empty. Imported modules are looked up in
/// `dir`; `threads`: threads for behaviours and `par` (1: the deterministic
/// FIFO scheduler, D67).
pub fn run(name: &str, text: &str, dir: &std::path::Path, args: &[String], unverified: bool, threads: usize) -> Ran {
    let (e, main, staged, report) = match ready_to_run(name, text, dir, unverified) {
        Ok(r) => r,
        Err(ran) => return ran,
    };
    eprint!("{report}");
    let code = native::run(&e.g, Some(&staged), main, args, threads);
    Ran { report: String::new(), code: code as u8 }
}

/// `checkers build`: check and prove, then write an executable.
pub fn build(name: &str, text: &str, dir: &std::path::Path, out: &std::path::Path, unverified: bool, release: bool) -> Ran {
    let (e, main, staged, mut report) = match ready_to_run(name, text, dir, unverified) {
        Ok(r) => r,
        Err(ran) => return ran,
    };
    // A release build relies on no `admit` anywhere in the program, its
    // dependencies or the standard library (§7.4, D116); axioms stay allowed.
    if release && !e.admits.is_empty() {
        let mut admits: Vec<&elab::Trusted> = e.admits.iter().collect();
        admits.sort_by(|a, b| (a.module.as_str(), a.span.start).cmp(&(b.module.as_str(), b.span.start)));
        for a in &admits {
            let d = Diagnostic::error("E0455", "a release build can't rely on an `admit`", a.span)
                .with_label(format!("assumed, not proven: {}", a.what.trim_start_matches("admit: ")))
                .with_help("prove it, or build without `--release`");
            report += &match e.sources.get(&a.module) {
                Some(f) => d.render(f),
                None => format!("error[E0455]: a release build can't rely on an `admit` ({}: {})\n", a.module, a.what),
            };
            report.push('\n');
        }
        report += &format!("error: `--release` refuses this program: it relies on {} `admit`{}\n", admits.len(), if admits.len() == 1 { "" } else { "s" });
        return Ran { report, code: 1 };
    }
    match native::build(&e.g, Some(&staged), main, out) {
        Ok(()) => Ran { report, code: 0 },
        Err(msg) => {
            report += &format!("error: {msg}\n");
            Ran { report, code: 2 }
        }
    }
}

/// Check, prove and stage a program for running: the elaborated program,
/// `main`, the staged code, and the report so far.
fn ready_to_run(
    name: &str,
    text: &str,
    dir: &std::path::Path,
    unverified: bool,
) -> Result<(elab::Elab, core::DefId, stage::Staged, String), Ran> {
    let (mut c, e) = elaborate(name, text, dir);
    let Some((e, user)) = e else { return Err(Ran { report: c.report(), code: 2 }) };
    run_checks(&mut c, &e, &user);
    prove(&mut c, &e, &user);
    let mut report = if c.all_diags().next().is_none() && c.internal.is_empty() { String::new() } else { c.report() };
    let blocking = c.internal.len() + c.all_diags().filter(|d| d.is_error() && !(unverified && is_proof_failure(d))).count();
    if blocking > 0 {
        return Err(Ran { report, code: 2 });
    }
    if c.errors() > 0 {
        report += &format!("running with {} unproven obligation(s) (--unverified)\n", c.errors());
    }
    let exported = e.modules.get(&user).is_some_and(|m| m.exported_values.contains("main"));
    let main = e.g.defs.iter().position(|d| *d.module == user && &*d.name == "main");
    let (Some(main), true) = (main, exported) else {
        return Err(Ran { report: format!("{report}error: `{}` has no exported `main` function\n", c.file.name), code: 2 });
    };
    let (staged, _) = stage::stage_program(&e.g);
    Ok((e, core::DefId(main as u32), staged, report))
}

/// Run `f` on a thread with a large stack: checking recurses deeply (long
/// lists in types, deep terms).
pub fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("spawn the checking thread")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e))
}
