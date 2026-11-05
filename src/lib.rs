//! The Checkers compiler. See SPEC.md for the language definition.
//!
//! Pipeline (M1): lex (with layout) → parse → naming lints → elaborate and
//! type-check (with the embedded standard library) → termination and usage.

pub mod core;
pub mod diag;
pub mod elab;
pub mod lint;
pub mod source;
pub mod syntax;
pub mod usage;

use diag::Diagnostic;
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

/// Run every implemented phase over one source file.
pub fn check(name: &str, text: &str) -> Checked {
    let mut c = parse_only(name, text);
    if c.diags.iter().any(|d| d.is_error()) {
        return c; // type checking a broken parse only produces noise
    }
    let stem = std::path::Path::new(name).file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let e = elab::check_module(&stem, &c.file, &c.module);
    let user = c.module.name.as_ref().map(|q| q.dotted()).unwrap_or(stem);
    for (m, d) in e.diags {
        if m == user {
            c.diags.push(d);
        } else {
            let rendered = match e.sources.get(&m) {
                Some(f) => d.render(f),
                None => format!("{}: {}\n", m, d.message),
            };
            c.internal.push(format!("internal error (standard library module `{m}`):\n{rendered}"));
        }
    }
    c.obligations = e.obligations.iter().filter(|o| o.module == user).count();
    c
}
