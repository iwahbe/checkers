//! The Checkers compiler. See SPEC.md for the language definition.
//!
//! Pipeline today (M0): lex (with layout) → parse → naming lints.

pub mod diag;
pub mod lint;
pub mod source;
pub mod syntax;

use diag::Diagnostic;
use source::SourceFile;

/// Result of checking one file.
pub struct Checked {
    pub file: SourceFile,
    pub module: syntax::ast::Module,
    pub diags: Vec<Diagnostic>,
}

impl Checked {
    pub fn errors(&self) -> usize {
        self.diags.iter().filter(|d| d.is_error()).count()
    }

    pub fn warnings(&self) -> usize {
        self.diags.len() - self.errors()
    }

    /// Diagnostics in source order, then a one-line summary.
    pub fn report(&self) -> String {
        let mut out = diag::render_all(&self.file, &self.diags);
        if !out.is_empty() {
            out.push('\n');
        }
        out += &format!(
            "{}: {} error{}, {} warning{}\n",
            self.file.name,
            self.errors(),
            if self.errors() == 1 { "" } else { "s" },
            self.warnings(),
            if self.warnings() == 1 { "" } else { "s" },
        );
        out
    }
}

/// Run every implemented phase over one source file.
pub fn check(name: &str, text: &str) -> Checked {
    let file = SourceFile::new(name, text);
    let (module, mut diags) = syntax::parse_module(text);
    diags.extend(lint::naming(&module));
    Checked { file, module, diags }
}
