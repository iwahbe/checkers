//! Surface syntax: lexer (with layout), parser, AST, and AST printer.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod print;
pub mod token;

use crate::diag::Diagnostic;

/// Lex and parse a whole file. Always returns a (possibly partial) module.
pub fn parse_module(text: &str) -> (ast::Module, Vec<Diagnostic>) {
    let (toks, mut diags) = lexer::lex(text);
    let (m, pdiags) = parser::parse(toks);
    diags.extend(pdiags);
    (m, diags)
}
