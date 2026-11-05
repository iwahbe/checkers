//! Diagnostics: errors and warnings with source spans, rendered rustc-style.

use crate::source::{SourceFile, Span};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    /// Stable code such as `W001` (warnings) or `E0100` (errors).
    pub code: &'static str,
    pub message: String,
    pub span: Span,
    /// Short text printed under the caret line.
    pub label: Option<String>,
    pub help: Option<String>,
}

impl Diagnostic {
    pub fn error(code: &'static str, message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic { severity: Severity::Error, code, message: message.into(), span, label: None, help: None }
    }

    pub fn warning(code: &'static str, message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic { severity: Severity::Warning, code, message: message.into(), span, label: None, help: None }
    }

    pub fn with_label(mut self, label: impl Into<String>) -> Diagnostic {
        self.label = Some(label.into());
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Diagnostic {
        self.help = Some(help.into());
        self
    }

    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    /// Render one diagnostic against its source file.
    ///
    /// ```text
    /// warning[W001]: type name `json` should be UpperCamelCase
    ///  --> json.ck:3:6
    ///   |
    /// 3 | enum json
    ///   |      ^^^^ rename to `Json`
    /// ```
    pub fn render(&self, file: &SourceFile) -> String {
        let kind = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let (line, col) = file.line_col(self.span.start);
        let (end_line, end_col) = file.line_col(self.span.end);
        let text = file.line_text(line);
        let gutter = line.to_string().len();
        let pad = " ".repeat(gutter);

        let mut out = format!("{kind}[{}]: {}\n", self.code, self.message);
        out += &format!("{pad}--> {}:{line}:{col}\n", file.name);
        out += &format!("{pad} |\n");
        out += &format!("{line} | {text}\n");
        let width = if end_line == line {
            end_col.saturating_sub(col).max(1)
        } else {
            text.chars().count().saturating_sub(col - 1).max(1)
        };
        let lead: String = text
            .chars()
            .take(col - 1)
            .map(|c| if c == '\t' { '\t' } else { ' ' })
            .collect();
        out += &format!("{pad} | {lead}{}", "^".repeat(width));
        if let Some(label) = &self.label {
            out += &format!(" {label}");
        }
        out += "\n";
        if let Some(help) = &self.help {
            out += &format!("{pad} = help: {help}\n");
        }
        out
    }
}

/// Render all diagnostics, in source order, separated by blank lines.
pub fn render_all(file: &SourceFile, diags: &[Diagnostic]) -> String {
    let mut sorted: Vec<&Diagnostic> = diags.iter().collect();
    sorted.sort_by_key(|d| (d.span.start, d.span.end));
    sorted.iter().map(|d| d.render(file)).collect::<Vec<_>>().join("\n")
}
