//! Source files and byte-offset spans.

use std::fmt;

/// A half-open byte range `[start, end)` into a source file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        Span { start: start as u32, end: end as u32 }
    }

    /// The smallest span covering both `self` and `other`.
    pub fn to(self, other: Span) -> Span {
        Span { start: self.start.min(other.start), end: self.end.max(other.end) }
    }

    pub fn empty_at(pos: u32) -> Span {
        Span { start: pos, end: pos }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// A source file with precomputed line starts for span → line/column lookup.
pub struct SourceFile {
    pub name: String,
    pub text: String,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> SourceFile {
        let text = text.into();
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        SourceFile { name: name.into(), text, line_starts }
    }

    /// 1-based line and 1-based column (in characters) of a byte offset.
    pub fn line_col(&self, offset: u32) -> (usize, usize) {
        let offset = (offset as usize).min(self.text.len());
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let start = self.line_starts[line];
        let col = self.text[start..offset].chars().count();
        (line + 1, col + 1)
    }

    /// 0-based line and 0-based column in bytes of a byte offset (§15.5).
    /// The byte offset of `[line, column]` (from 0, the column in bytes),
    /// if it is in the file.
    pub fn offset(&self, line: usize, col: usize) -> Option<usize> {
        let start = *self.line_starts.get(line)?;
        let end = self.line_starts.get(line + 1).map_or(self.text.len(), |e| e - 1);
        (start + col <= end.max(start)).then_some(start + col)
    }

    pub fn line_byte(&self, offset: u32) -> (usize, usize) {
        let offset = (offset as usize).min(self.text.len());
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        (line, offset - self.line_starts[line])
    }

    /// The text of a 1-based line, without its newline.
    pub fn line_text(&self, line: usize) -> &str {
        let start = self.line_starts[line - 1];
        let end = self
            .line_starts
            .get(line)
            .map(|e| e - 1)
            .unwrap_or(self.text.len());
        self.text[start..end].trim_end_matches('\r')
    }

    pub fn slice(&self, span: Span) -> &str {
        &self.text[span.start as usize..span.end as usize]
    }
}
