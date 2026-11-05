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
pub mod syntax;
pub mod usage;

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
    /// Predicates recorded for the prover (M3), in this file.
    pub obligations: usize,
}

impl Checked {
    pub fn errors(&self) -> usize {
        self.diags.iter().filter(|d| d.is_error()).count() + self.internal.len()
    }

    pub fn warnings(&self) -> usize {
        self.diags.iter().filter(|d| !d.is_error()).count()
    }

    /// Diagnostics in source order, then a one-line summary.
    pub fn report(&self) -> String {
        let mut out = diag::render_all(&self.file, &self.diags);
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
        if self.obligations > 0 && self.errors() == 0 {
            out += &format!(
                "; {} proof obligation{} recorded for the prover",
                self.obligations,
                if self.obligations == 1 { "" } else { "s" }
            );
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
    Checked { file, module, diags, internal: Vec::new(), obligations: 0 }
}

/// Run every implemented phase over one source file, including its `check`s.
pub fn check(name: &str, text: &str) -> Checked {
    let (mut c, e) = elaborate(name, text);
    if let Some((e, user)) = &e {
        run_checks(&mut c, e, user);
    }
    c
}

/// Parse, lint and type-check; also returns the elaborator and the module name.
fn elaborate(name: &str, text: &str) -> (Checked, Option<(elab::Elab, String)>) {
    let mut c = parse_only(name, text);
    if c.diags.iter().any(|d| d.is_error()) {
        return (c, None); // type checking a broken parse only produces noise
    }
    let stem = std::path::Path::new(name).file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let e = elab::check_module(&stem, &c.file, &c.module);
    let user = c.module.name.as_ref().map(|q| q.dotted()).unwrap_or(stem);
    for (m, d) in &e.diags {
        if *m == user {
            c.diags.push(d.clone());
        } else {
            let rendered = match e.sources.get(m) {
                Some(f) => d.render(f),
                None => format!("{}: {}\n", m, d.message),
            };
            c.internal.push(format!("internal error (standard library module `{m}`):\n{rendered}"));
        }
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
    for (m, span, t) in &e.checks {
        if m != user {
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
                c.diags.push(d);
            }
            Ok(_) => {}
            Err(err) => c.diags.push(
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

/// Check `text`, then call its exported `main` with `args` (D43, §13.4).
pub fn run(name: &str, text: &str, args: &[String], io: run::Io) -> Ran {
    let (mut c, e) = elaborate(name, text);
    let Some((e, user)) = e else { return Ran { report: c.report(), code: 2 } };
    run_checks(&mut c, &e, &user);
    let report = if c.diags.is_empty() && c.internal.is_empty() { String::new() } else { c.report() };
    if c.errors() > 0 {
        return Ran { report, code: 2 };
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
