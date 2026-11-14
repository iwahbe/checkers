//! Surface syntax: lexer (with layout), parser, AST, and AST printer.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod print;
pub mod token;

use crate::diag::Diagnostic;

/// Lex and parse a whole file. Always returns a (possibly partial) module.
/// `parse_module` with the cursor at byte `at` (D142): also the kind of
/// place it is in, and the span of the text it replaces. None if completion
/// doesn't apply there (in a comment or a literal).
pub fn parse_at_cursor(text: &str, at: usize) -> Option<(ast::Module, Option<parser::Place>, crate::source::Span)> {
    let (toks, _, replaced) = lexer::lex_with_cursor(text, at)?;
    let (m, _, place) = parser::parse_with_place(toks);
    Some((m, place, replaced))
}

pub fn parse_module(text: &str) -> (ast::Module, Vec<Diagnostic>) {
    let (toks, mut diags) = lexer::lex(text);
    let (m, pdiags) = parser::parse(toks);
    diags.extend(pdiags);
    (m, diags)
}
