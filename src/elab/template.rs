//! Templates (#132): `tag"a{x}b{y | o}c"` is calls of `std.string`'s
//! `Template` and `Hole` classes' functions, one for each piece:
//!
//! ```text
//! finish (text (hole (text (hole (text (tag 3 2) "a") x []) "b") y [o]) "c")
//! ```
//!
//! the tag's first state bound once, and, with positional holes (`{}`), a
//! lambda taking them in order.

use super::*;
use super::classes::HeadKey;
use crate::syntax::ast::{Expr, ExprKind, TemplatePiece};

/// The names a template's calls use: `std.string`'s class functions (no
/// user name can start with `$`), whether or not the module imports them.
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

/// `s` without parentheses around all of it.
fn unparen(s: &str) -> String {
    let b = s.as_bytes();
    if b.first() != Some(&b'(') || b.last() != Some(&b')') {
        return s.to_string();
    }
    let mut depth = 0;
    for (i, c) in b.iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 && i + 1 < b.len() {
                    return s.to_string();
                }
            }
            _ => {}
        }
    }
    unparen(s[1..s.len() - 1].trim())
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
        let m = self.modules.get("std.string")?;
        match m.values.get(n) {
            Some(s @ Sym::Def(_)) => Some(*s),
            _ => None,
        }
    }

    /// `std.string`'s definition `name`, if it is loaded.
    pub(super) fn std_def(&self, name: &str) -> Option<DefId> {
        match self.modules.get("std.string")?.values.get(name) {
            Some(Sym::Def(d)) => Some(*d),
            _ => None,
        }
    }

    /// Help for an unknown name that the standard library exports: the
    /// import that brings it in.
    pub(super) fn std_export_help(&self, n: &str) -> Option<String> {
        let ms = crate::elab::stdlib::exporters(n);
        let first = ms.first()?;
        let others = ms[1..].iter().map(|m| format!("`{m}`")).collect::<Vec<_>>();
        let rest = if others.is_empty() { String::new() } else { format!(" (or {})", others.join(", ")) };
        Some(format!("`{n}` is in `{first}`: add `import {first} ({n})`{rest}"))
    }

    /// A call of a template's tag, `tag x` (#126): a function whose result
    /// has a `Template` instance, called outside a template. A type error
    /// at the call or at its first argument gets a help line saying so.
    pub(super) fn note_tag_call(&mut self, head: &Expr, ft: &Val, call: Span, arg: &Expr) {
        let ExprKind::Var(n) = &head.kind else { return };
        if self.in_tag {
            return;
        }
        let Some(Sym::Ty(class)) = self.modules.get("std.string").and_then(|m| m.types.get("Template")).copied() else { return };
        let mut ty = self.force(ft);
        let mut lvl = 0;
        while let Val::Pi(_, _, _, _, c) = ty {
            ty = self.force(&apply_closure(&self.g, &c, Val::var(lvl)));
            lvl += 1;
        }
        let Val::TyCon(id, _) = ty else { return };
        if !self.instances.contains_key(&(class, HeadKey::Ty(id))) {
            return;
        }
        let x = unparen(self.src_text(arg.span).trim());
        let help = format!("`{n}` is a template's tag: write `{n}\"…{{{x}}}…\"` to put `{x}` in a template");
        for s in [call, arg.span] {
            self.tag_calls.insert((self.cur.clone(), s.start, s.end), help.clone());
        }
    }

    /// Whether a generated name is one of the classes' functions, which
    /// the index leaves out: what is written at their spans is the tag or
    /// a hole's value.
    pub(super) fn is_template_call(name: &str) -> bool {
        matches!(name, TEXT | HOLE | FINISH)
    }

    /// Check (with `expected`) or infer the template `e`.
    ///
    /// With positional holes it is a lambda around the same template, its
    /// holes holding the lambda's parameters. Otherwise the tag's first
    /// state, `tag n k`, is elaborated first and bound to a local: if that
    /// fails, or its type can't have a `Template` instance, that is the
    /// only error, and the holes aren't checked against a formatter that
    /// doesn't exist.
    pub(super) fn elab_template(&mut self, cx: &mut Cx, e: &Expr, expected: Option<&Val>) -> (Tm, Val) {
        let ExprKind::Template(tag, pieces) = &e.kind else { unreachable!() };
        let mut params = Vec::new();
        let filled: Vec<TemplatePiece> = pieces
            .iter()
            .map(|p| match p {
                TemplatePiece::Hole { value: None, options, span } => {
                    let n = format!("$hole{}", params.len());
                    params.push(ast::Pattern { kind: ast::PatKind::Var(n.clone()), span: *span });
                    TemplatePiece::Hole { value: Some(var(&n, *span)), options: options.clone(), span: *span }
                }
                p => p.clone(),
            })
            .collect();
        if !params.is_empty() {
            let inner = mk(ExprKind::Template(tag.clone(), filled), e.span);
            let lam = mk(ExprKind::Lambda(params, Box::new(inner)), e.span);
            return match expected {
                Some(ty) => (self.check(cx, &lam, ty, false), ty.clone()),
                None => self.infer(cx, &lam),
            };
        }
        let bytes: usize = pieces
            .iter()
            .map(|p| match p {
                TemplatePiece::Text(s, _) => s.len(),
                TemplatePiece::Hole { .. } => 0,
            })
            .sum();
        let ts = tag.span;
        let holes = pieces.iter().filter(|p| matches!(p, TemplatePiece::Hole { .. })).count();
        // The sizes are the literal's: an error about them (a tag that
        // isn't a function, or takes other arguments) points at it.
        let lit = Span { start: ts.end, end: e.span.end };
        let first = app(app((**tag).clone(), int(bytes, lit), e.span), int(holes, lit), e.span);
        let saved = std::mem::replace(&mut self.in_tag, true);
        let (t0, ty0) = self.infer(cx, &first);
        self.in_tag = saved;
        if matches!(t0, Tm::Error) {
            return (Tm::Error, Val::Error);
        }
        let ty0 = self.reduce_type(&ty0);
        if !self.may_be_formatter(cx, &ty0) {
            if !matches!(ty0, Val::Error) {
                let shown = self.show_val(cx, &ty0);
                let tag_text = self.src_text(ts);
                let param = matches!(self.force(&ty0), Val::Neutral(Head::Var(_), _));
                let help = if param {
                    format!("add `Template {shown}` to the function's signature (`Template` is `std.string`'s)")
                } else {
                    "a tag gives a formatter: a type with an instance of `Template` (from `std.string`)".to_string()
                };
                self.err(
                    Diagnostic::error("E0284", format!("no instance of `Template` for `{shown}`: `{tag_text}` isn't a template's tag"), ts)
                        .with_label(format!("its result is `{shown}`"))
                        .with_help(help),
                );
            }
            return (Tm::Error, Val::Error);
        }
        // The state, bound once; each piece's call takes the one before.
        let name = "$tpl#state";
        let mult = self.named_mult(cx, name, &ty0, ts, Mult::Many);
        let v = self.eval(cx, &t0);
        let tyt = quote(&self.g, cx.lvl(), &ty0);
        cx.define_by(name, ty0, v, mult, t0.clone());
        let mut st = var(name, ts);
        for p in pieces {
            match p {
                TemplatePiece::Text(s, sp) => {
                    let lit = mk(ExprKind::Lit(ast::Lit::Str(s.clone())), *sp);
                    st = app(app(var(TEXT, ts), st, *sp), lit, *sp);
                }
                TemplatePiece::Hole { value, options, span } => {
                    let v = value.clone().expect("positional holes are parameters by now");
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
        let (bt, bty) = match expected {
            Some(ty) => (self.check(cx, &body, ty, false), ty.clone()),
            None => self.infer(cx, &body),
        };
        cx.pop();
        let bty = crate::core::strengthen(&self.g, &bty, cx.lvl());
        (Tm::Let(Rc::from(name), mult, Rc::new(tyt), Rc::new(t0), Rc::new(bt)), bty)
    }

    /// Whether `ty` may have an instance of `Template`: an instance for
    /// its type constructor, a dictionary in scope for it, or not known
    /// yet (the instance is then looked for once it is).
    fn may_be_formatter(&self, cx: &Cx, ty: &Val) -> bool {
        let Some(Sym::Ty(class)) = self.modules.get("std.string").and_then(|m| m.types.get("Template")).copied() else {
            return true;
        };
        let has = |k: HeadKey| self.instances.contains_key(&(class, k));
        match self.force(ty) {
            Val::Neutral(Head::Meta(_), _) => true,
            Val::TyCon(id, _) => has(HeadKey::Ty(id)),
            Val::TupleTy(xs) if xs.is_empty() => has(HeadKey::Unit),
            Val::TupleTy(_) => has(HeadKey::Pair),
            t @ Val::Neutral(..) => {
                // A type parameter: a dictionary of `Template` for it.
                let tq = format!("{:?}", quote(&self.g, cx.lvl(), &t));
                cx.locals.iter().any(|loc| match self.force(&loc.ty) {
                    Val::TyCon(c, a) if c == class => a.last().is_some_and(|x| format!("{:?}", quote(&self.g, cx.lvl(), &self.force(x))) == tq),
                    _ => false,
                })
            }
            _ => false,
        }
    }
}
