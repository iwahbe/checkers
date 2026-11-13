//! Naming-convention warnings (§9.7, D21).
//!
//! W001  UpperCamelCase      enum / record / type names, constructors
//! W002  lower_snake_case    functions, lemmas, parameters, variables, fields, modules, aliases
//! W003  SCREAMING_SNAKE     top-level `let` constants

use crate::diag::Diagnostic;
use crate::syntax::ast::*;

pub fn naming(m: &Module) -> Vec<Diagnostic> {
    let mut l = Linter { diags: Vec::new() };
    if let Some(q) = &m.name {
        for p in &q.parts {
            l.snake(p, "module name");
        }
    }
    for i in &m.imports {
        if let Some(a) = &i.alias {
            l.snake(a, "import alias");
        }
    }
    for d in &m.decls {
        l.decl(d);
    }
    l.diags
}

struct Linter {
    diags: Vec<Diagnostic>,
}

fn core(name: &str) -> &str {
    name.trim_start_matches('_')
}

pub fn is_upper_camel(name: &str) -> bool {
    let n = core(name);
    n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) && !n.contains('_')
}

pub fn is_lower_snake(name: &str) -> bool {
    let n = core(name);
    n.is_empty()
        || (n.chars().next().is_some_and(|c| c.is_ascii_lowercase())
            && n.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_'))
}

pub fn is_screaming(name: &str) -> bool {
    let n = core(name);
    n.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        && n.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
}

/// Split an identifier into lowercase words, at `_` and at case boundaries.
fn words(name: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut cur = String::new();
    let chars: Vec<char> = core(name).chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        if c == '_' {
            if !cur.is_empty() {
                out.push(std::mem::take(&mut cur));
            }
            continue;
        }
        let boundary = c.is_ascii_uppercase()
            && i > 0
            && (chars[i - 1].is_ascii_lowercase()
                || chars[i - 1].is_ascii_digit()
                || (chars[i - 1].is_ascii_uppercase() && chars.get(i + 1).is_some_and(|n| n.is_ascii_lowercase())));
        if boundary && !cur.is_empty() {
            out.push(std::mem::take(&mut cur));
        }
        cur.push(c.to_ascii_lowercase());
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

pub fn to_upper_camel(name: &str) -> String {
    words(name)
        .iter()
        .map(|w| {
            let mut c = w.chars();
            match c.next() {
                Some(f) => f.to_ascii_uppercase().to_string() + c.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

pub fn to_lower_snake(name: &str) -> String {
    words(name).join("_")
}

pub fn to_screaming(name: &str) -> String {
    words(name).join("_").to_ascii_uppercase()
}

impl Linter {
    fn camel(&mut self, id: &Ident, what: &str) {
        if !is_upper_camel(&id.name) {
            let fix = to_upper_camel(&id.name);
            self.diags.push(
                Diagnostic::warning("W001", format!("{what} `{}` should be UpperCamelCase", id.name), id.span)
                    .with_label(format!("rename to `{fix}`")),
            );
        }
    }

    fn snake(&mut self, id: &Ident, what: &str) {
        if !is_lower_snake(&id.name) {
            let fix = to_lower_snake(&id.name);
            self.diags.push(
                Diagnostic::warning("W002", format!("{what} `{}` should be lower_snake_case", id.name), id.span)
                    .with_label(format!("rename to `{fix}`")),
            );
        }
    }

    fn screaming(&mut self, id: &Ident) {
        if !is_screaming(&id.name) {
            let fix = to_screaming(&id.name);
            self.diags.push(
                Diagnostic::warning(
                    "W003",
                    format!("constant `{}` should be SCREAMING_SNAKE_CASE", id.name),
                    id.span,
                )
                .with_label(format!("rename to `{fix}`")),
            );
        }
    }

    fn constraints(&mut self, cs: &[Constraint]) {
        for c in cs {
            match c {
                Constraint::Typed { ty, .. } => self.expr(ty),
                Constraint::Pred(e) | Constraint::Named(_, e) => self.expr(e),
            }
        }
    }

    fn decl(&mut self, d: &Decl) {
        match &d.kind {
            DeclKind::Fn { name, params, result, constraints, decreasing, body, .. } => {
                self.snake(name, "function name");
                for p in params {
                    self.snake(p, "parameter");
                }
                if let Some(r) = result {
                    self.snake(r, "result name");
                }
                self.constraints(constraints);
                if let Some(e) = decreasing {
                    self.expr(e);
                }
                self.block(body);
            }
            DeclKind::Enum { name, params, constraints, ctors } => {
                self.camel(name, "enum name");
                for p in params {
                    self.snake(&p.name, "type parameter");
                }
                self.constraints(constraints);
                for c in ctors {
                    self.camel(&c.name, "constructor");
                    for p in &c.params {
                        self.snake(p, "constructor field");
                    }
                    self.constraints(&c.constraints);
                }
            }
            DeclKind::Record { name, params, constraints, fields } => {
                self.camel(name, "record name");
                for p in params {
                    self.snake(&p.name, "type parameter");
                }
                self.constraints(constraints);
                for f in fields {
                    self.snake(&f.name, "field");
                    self.expr(&f.ty);
                    for p in &f.preds {
                        self.expr(p);
                    }
                }
            }
            DeclKind::Alias { name, params, constraints } => {
                self.camel(name, "type name");
                for p in params {
                    self.snake(p, "type parameter");
                }
                if let Some(Constraint::Typed { name, .. }) = constraints.first() {
                    self.snake(name, "binder");
                }
                self.constraints(constraints);
            }
            DeclKind::Lemma { name, params, constraints, lets, ensures, proof } => {
                self.snake(name, "lemma name");
                for p in params {
                    self.snake(p, "parameter");
                }
                self.constraints(constraints);
                for (p, e) in lets {
                    self.pat(p);
                    self.expr(e);
                }
                self.expr(ensures);
                if let Some(b) = proof {
                    self.block(b);
                }
            }
            DeclKind::Const { name, value } => {
                self.screaming(name);
                self.expr(value);
            }
            DeclKind::Check { expr } => self.expr(expr),
            DeclKind::Class { name, param, members } => {
                self.camel(name, "class name");
                self.snake(param, "type parameter");
                for m in members {
                    match m {
                        ClassMember::Fn { name, params, constraints, .. } => {
                            self.snake(name, "function name");
                            params.iter().for_each(|p| self.snake(p, "parameter"));
                            self.constraints(constraints);
                        }
                        ClassMember::Lemma { name, params, constraints, ensures, .. } => {
                            self.snake(name, "lemma name");
                            params.iter().for_each(|p| self.snake(p, "parameter"));
                            self.constraints(constraints);
                            self.expr(ensures);
                        }
                    }
                }
            }
            DeclKind::Instance { members, .. } => {
                for m in members {
                    match m {
                        InstMember::Fn { params, body, .. } => {
                            params.iter().for_each(|p| self.snake(p, "parameter"));
                            self.block(body);
                        }
                        InstMember::Lemma { params, proof, .. } => {
                            params.iter().for_each(|p| self.snake(p, "parameter"));
                            if let Some(b) = proof {
                                self.block(b);
                            }
                        }
                    }
                }
            }
        }
    }

    fn block(&mut self, b: &Block) {
        for s in &b.stmts {
            match s {
                Stmt::Let(p, e) => {
                    self.pat(p);
                    self.expr(e);
                }
                Stmt::Have(e) | Stmt::Expr(e) => self.expr(e),
                Stmt::Bind(p, e) => {
                    self.pat(p);
                    self.expr(e);
                }
                Stmt::When(w) => {
                    for (n, c) in &w.binds {
                        self.snake(n, "variable");
                        self.expr(c);
                    }
                    self.block(&w.body);
                }
            }
        }
        self.expr(&b.result);
    }

    fn pat(&mut self, p: &Pattern) {
        match &p.kind {
            PatKind::Var(n) => self.snake(&Ident { name: n.clone(), span: p.span }, "variable"),
            PatKind::Con(_, args) => args.iter().for_each(|a| self.pat(a)),
            PatKind::Tuple(v) | PatKind::List(v) | PatKind::Or(v) => v.iter().for_each(|a| self.pat(a)),
            PatKind::Cons(h, t) => {
                self.pat(h);
                self.pat(t);
            }
            PatKind::Record(_, fs) => fs.iter().for_each(|(_, p)| self.pat(p)),
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Unit => {}
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Tuple(v) | ExprKind::List(v) | ExprKind::Par(v) => v.iter().for_each(|x| self.expr(x)),
            ExprKind::App(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) | ExprKind::Index(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Neg(x) | ExprKind::SectionL(_, x) | ExprKind::SectionR(_, x) | ExprKind::Try(x) => self.expr(x),
            ExprKind::Field(x, _) => self.expr(x),
            ExprKind::Forall(vs, cs) => {
                vs.iter().for_each(|v| self.snake(v, "variable"));
                self.constraints(cs);
            }
            ExprKind::Refine(r) => {
                r.types().into_iter().for_each(|t| self.expr(t));
                r.preds.iter().for_each(|p| self.expr(p));
            }
            ExprKind::If(c, t, f) => {
                self.expr(c);
                self.expr(t);
                self.expr(f);
            }
            ExprKind::Match(s, arms) => {
                self.expr(s);
                for a in arms {
                    self.pat(&a.pat);
                    if let Some(g) = &a.guard {
                        self.expr(g);
                    }
                    self.expr(&a.body);
                }
            }
            ExprKind::Lambda(ps, b) => {
                ps.iter().for_each(|p| self.pat(p));
                self.expr(b);
            }
            ExprKind::Block(b) | ExprKind::Fork(_, b) => self.block(b),
            ExprKind::Join(binds, _, b) => {
                for (n, f) in binds {
                    self.snake(n, "variable");
                    self.expr(f);
                }
                self.block(b);
            }
            ExprKind::Var(_)
            | ExprKind::Con(_)
            | ExprKind::Lit(_)
            | ExprKind::Unit
            | ExprKind::OpRef(_)
            | ExprKind::Auto
            | ExprKind::Admit
            | ExprKind::Error => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conversions() {
        assert_eq!(to_upper_camel("json_value"), "JsonValue");
        assert_eq!(to_upper_camel("HTTPServer"), "HttpServer");
        assert_eq!(to_lower_snake("parseHTTPRequest"), "parse_http_request");
        assert_eq!(to_screaming("maxDepth"), "MAX_DEPTH");
        assert_eq!(to_screaming("max_depth"), "MAX_DEPTH");
        assert!(is_upper_camel("U8") && is_upper_camel("Json") && !is_upper_camel("MAX_DEPTH"));
        assert!(is_lower_snake("hex4") && is_lower_snake("_unused") && !is_lower_snake("hexValue"));
        assert!(is_screaming("MAX_DEPTH") && is_screaming("PI") && !is_screaming("Pi"));
    }
}
