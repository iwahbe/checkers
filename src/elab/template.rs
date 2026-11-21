//! Templates (#132): `tag"a{x}b{y | o}c"` is calls of the prelude's
//! `Template` and `Hole` classes' functions, one for each piece:
//!
//! ```text
//! finish (text (hole (text (hole (text (tag 3 2) "a") x []) "b") y [o]) "c")
//! ```
//!
//! and, with positional holes (`{}`), a lambda taking them in order.

use super::*;
use crate::syntax::ast::{Expr, ExprKind, TemplatePiece};

/// The names a template's calls use: the prelude's class functions (no
/// user name can start with `$`).
pub const TEXT: &str = "$tpl#text";
pub const HOLE: &str = "$tpl#hole";
pub const FINISH: &str = "$tpl#finish";

fn mk(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn var(n: &str, span: Span) -> Expr {
    mk(ExprKind::Var(n.to_string()), span)
}

fn app(f: Expr, a: Expr, span: Span) -> Expr {
    mk(ExprKind::App(Box::new(f), Box::new(a)), span)
}

fn int(n: usize, span: Span) -> Expr {
    mk(ExprKind::Lit(ast::Lit::Int(n.to_string())), span)
}

impl Elab {
    /// The definition a template's generated name stands for.
    pub(super) fn template_sym(&self, name: &str) -> Option<Sym> {
        let n = match name {
            TEXT => "text",
            HOLE => "hole",
            FINISH => "finish",
            _ => return None,
        };
        let m = self.modules.get("std.prelude")?;
        match m.values.get(n) {
            Some(s @ Sym::Def(_)) => Some(*s),
            _ => None,
        }
    }

    /// Whether a generated name is one of the classes' functions, which
    /// the index leaves out: what is written at their spans is the tag or
    /// a hole's value.
    pub(super) fn is_template_call(name: &str) -> bool {
        matches!(name, TEXT | HOLE | FINISH)
    }

    /// The template `e` as calls (see the module's comment). Each call's
    /// span is the piece it builds, and a class function's name has the
    /// span of what chooses its instance: the tag for `text` and `finish`,
    /// a hole's value (or the hole, without one) for `hole`.
    pub(super) fn desugar_template(&self, e: &Expr) -> Expr {
        let ExprKind::Template(tag, pieces) = &e.kind else { unreachable!() };
        let bytes: usize = pieces
            .iter()
            .map(|p| match p {
                TemplatePiece::Text(s, _) => s.len(),
                TemplatePiece::Hole { .. } => 0,
            })
            .sum();
        let holes = pieces.iter().filter(|p| matches!(p, TemplatePiece::Hole { .. })).count();
        let ts = tag.span;
        let mut st = app(app((**tag).clone(), int(bytes, ts), ts), int(holes, ts), ts);
        let mut params = Vec::new();
        for p in pieces {
            match p {
                TemplatePiece::Text(s, sp) => {
                    let lit = mk(ExprKind::Lit(ast::Lit::Str(s.clone())), *sp);
                    st = app(app(var(TEXT, ts), st, *sp), lit, *sp);
                }
                TemplatePiece::Hole { value, options, span } => {
                    let v = match value {
                        Some(v) => v.clone(),
                        None => {
                            let n = format!("$hole{}", params.len());
                            params.push(ast::Pattern { kind: ast::PatKind::Var(n.clone()), span: *span });
                            var(&n, *span)
                        }
                    };
                    let os_span = match (options.first(), options.last()) {
                        (Some(a), Some(b)) => a.span.to(b.span),
                        _ => *span,
                    };
                    let os = mk(ExprKind::List(options.clone()), os_span);
                    st = app(app(app(var(HOLE, v.span), st, *span), v, *span), os, *span);
                }
            }
        }
        let body = app(var(FINISH, ts), st, e.span);
        if params.is_empty() {
            body
        } else {
            mk(ExprKind::Lambda(params, Box::new(body)), e.span)
        }
    }
}
