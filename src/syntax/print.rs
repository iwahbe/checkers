//! S-expression dump of the surface AST (`checkers parse`). Stable output for golden tests.

use super::ast::*;

pub fn module(m: &Module) -> String {
    let mut out = String::new();
    match &m.name {
        Some(q) => out += &format!("(module {})\n", q.dotted()),
        None => out += "(module ?)\n",
    }
    for i in &m.imports {
        out += &format!("(import {}", i.path.dotted());
        if let Some(items) = &i.items {
            out += &format!(" ({})", names(items));
        }
        if let Some(a) = &i.alias {
            out += &format!(" as {}", a.name);
        }
        out += ")\n";
    }
    for d in &m.decls {
        out += &decl(d);
        out += "\n";
    }
    out
}

fn names(v: &[Ident]) -> String {
    v.iter().map(|i| i.name.as_str()).collect::<Vec<_>>().join(" ")
}

fn ind(n: usize) -> String {
    "  ".repeat(n)
}

fn decl(d: &Decl) -> String {
    let ex = match d.export {
        Export::No => "",
        Export::Yes => "export ",
        Export::Abstract => "export-abstract ",
        Export::Transparent => "export-transparent ",
    };
    match &d.kind {
        DeclKind::Fn { partial, name, params, result, constraints, decreasing, body } => {
            let mut s = format!(
                "({ex}{}fn {} ({})",
                if *partial { "partial " } else { "" },
                name.name,
                names(params)
            );
            if let Some(r) = result {
                s += &format!(" -> {}", r.name);
            }
            s += &cons(constraints, 1);
            if let Some(e) = decreasing {
                s += &format!("\n{}(decreasing {})", ind(1), expr(e, 1));
            }
            s += &format!("\n{}{})", ind(1), block(body, 1));
            s
        }
        DeclKind::Enum { name, params, constraints, ctors } => {
            let mut s = format!("({ex}enum {} ({})", name.name, pnames(params));
            s += &cons(constraints, 1);
            for c in ctors {
                s += &format!("\n{}(ctor {} ({})", ind(1), c.name.name, names(&c.params));
                s += &cons(&c.constraints, 2);
                s += ")";
            }
            s + ")"
        }
        DeclKind::Record { name, params, constraints, fields } => {
            let mut s = format!("({ex}record {} ({})", name.name, pnames(params));
            s += &cons(constraints, 1);
            for f in fields {
                s += &format!("\n{}(field {}{} {}", ind(1), f.name.name, mult(f.mult), expr(&f.ty, 2));
                for p in &f.preds {
                    s += &format!(" {}", expr(p, 2));
                }
                s += ")";
            }
            s + ")"
        }
        DeclKind::Alias { name, params, constraints } => {
            format!("({ex}type {} ({}){})", name.name, names(params), cons(constraints, 1))
        }
        DeclKind::Lemma { name, params, constraints, lets, ensures, proof } => {
            let mut s = format!("({ex}lemma {} ({})", name.name, names(params));
            s += &cons(constraints, 1);
            for (p, e) in lets {
                s += &format!("\n{}(let {} {})", ind(1), pat(p), expr(e, 1));
            }
            s += &format!("\n{}(ensures {})", ind(1), expr(ensures, 1));
            if let Some(b) = proof {
                s += &format!("\n{}(proof {})", ind(1), block(b, 2));
            }
            s + ")"
        }
        DeclKind::Const { name, value } => format!("({ex}const {} {})", name.name, expr(value, 1)),
        DeclKind::Check { expr: e } => format!("(check {})", expr(e, 1)),
    }
}

fn pnames(ps: &[Param]) -> String {
    ps.iter()
        .map(|p| {
            let pol = match p.polarity {
                Some(Polarity::Pos) => "+",
                Some(Polarity::Neg) => "-",
                None => "",
            };
            format!("{pol}{}", p.name.name)
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn mult(m: Mult) -> &'static str {
    match m {
        Mult::Many => "",
        Mult::Ghost => " ghost",
        Mult::Own => " own",
    }
}

fn cons(cs: &[Constraint], depth: usize) -> String {
    if cs.is_empty() {
        return String::new();
    }
    let items: Vec<String> = cs
        .iter()
        .map(|c| match c {
            Constraint::Typed { name, mult: m, ty } => format!("({}~{} {})", name.name, mult(*m).trim(), expr(ty, depth))
                .replace("~ ", "~"),
            Constraint::Pred(e) => expr(e, depth),
        })
        .collect();
    format!("\n{}(: {})", ind(depth), items.join(" "))
}

fn block(b: &Block, depth: usize) -> String {
    let mut parts = Vec::new();
    for s in &b.stmts {
        parts.push(match s {
            Stmt::Let(p, e) => format!("(let {} {})", pat(p), expr(e, depth + 1)),
            Stmt::Have(e) => format!("(have {})", expr(e, depth + 1)),
        });
    }
    parts.push(expr(&b.result, depth + 1));
    if parts.len() == 1 {
        return parts.pop().unwrap();
    }
    format!("(do\n{}{})", ind(depth + 1), parts.join(&format!("\n{}", ind(depth + 1))))
}

fn lit(l: &Lit) -> String {
    match l {
        Lit::Int(s) => s.clone(),
        Lit::Byte(b) => format!("'{}'", escape_byte(*b)),
        Lit::Char(c) => format!("c'{}'", c.escape_default()),
        Lit::Str(s) => format!("{s:?}"),
        Lit::Bytes(b) => format!("b\"{}\"", b.iter().map(|b| escape_byte(*b)).collect::<String>()),
    }
}

fn escape_byte(b: u8) -> String {
    match b {
        b'\n' => "\\n".into(),
        b'\r' => "\\r".into(),
        b'\t' => "\\t".into(),
        b'\\' => "\\\\".into(),
        b'\'' => "\\'".into(),
        b'"' => "\\\"".into(),
        0x20..=0x7e => (b as char).to_string(),
        _ => format!("\\x{b:02x}"),
    }
}

pub fn expr(e: &Expr, depth: usize) -> String {
    match &e.kind {
        ExprKind::Var(n) | ExprKind::Con(n) => n.clone(),
        ExprKind::Lit(l) => lit(l),
        ExprKind::Unit => "()".into(),
        ExprKind::Tuple(v) => format!("(tuple {})", list(v, depth)),
        ExprKind::List(v) => format!("[{}]", list(v, depth)),
        ExprKind::App(f, a) => {
            // flatten curried application
            let mut args = vec![a.as_ref()];
            let mut head = f.as_ref();
            while let ExprKind::App(f2, a2) = &head.kind {
                args.push(a2);
                head = f2;
            }
            args.reverse();
            let args: Vec<String> = args.iter().map(|a| expr(a, depth)).collect();
            format!("({} {})", expr(head, depth), args.join(" "))
        }
        ExprKind::Binary(op, l, r) => format!("({} {} {})", op.as_str(), expr(l, depth), expr(r, depth)),
        ExprKind::Arrow(a, b) => format!("(-> {} {})", expr(a, depth), expr(b, depth)),
        ExprKind::Neg(x) => format!("(neg {})", expr(x, depth)),
        ExprKind::OpRef(op) => format!("({})", op.as_str()),
        ExprKind::SectionL(op, x) => format!("(section {} {} _)", op.as_str(), expr(x, depth)),
        ExprKind::SectionR(op, x) => format!("(section {} _ {})", op.as_str(), expr(x, depth)),
        ExprKind::Field(x, n) => format!("{}.{}", expr(x, depth), n.name),
        ExprKind::Index(x, i) => format!("(index {} {})", expr(x, depth), expr(i, depth)),
        ExprKind::If(c, t, f) => format!(
            "(if {}\n{}{}\n{}{})",
            expr(c, depth),
            ind(depth + 1),
            expr(t, depth + 1),
            ind(depth + 1),
            expr(f, depth + 1)
        ),
        ExprKind::Match(s, arms) => {
            let mut out = format!("(match {}", expr(s, depth));
            for a in arms {
                out += &format!("\n{}({}", ind(depth + 1), pat(&a.pat));
                if let Some(g) = &a.guard {
                    out += &format!(" if {}", expr(g, depth + 2));
                }
                out += &format!(" -> {})", expr(&a.body, depth + 2));
            }
            out + ")"
        }
        ExprKind::Lambda(ps, b) => format!(
            "(\\ ({}) {})",
            ps.iter().map(pat).collect::<Vec<_>>().join(" "),
            expr(b, depth)
        ),
        ExprKind::Try(x) => format!("(try {})", expr(x, depth)),
        ExprKind::Block(b) => block(b, depth),
        ExprKind::Auto => "auto".into(),
        ExprKind::Admit => "admit".into(),
        ExprKind::Error => "<error>".into(),
    }
}

fn list(v: &[Expr], depth: usize) -> String {
    v.iter().map(|e| expr(e, depth)).collect::<Vec<_>>().join(" ")
}

pub fn pat(p: &Pattern) -> String {
    match &p.kind {
        PatKind::Wild => "_".into(),
        PatKind::Var(n) => n.clone(),
        PatKind::Lit(l) => lit(l),
        PatKind::Neg(s) => format!("-{s}"),
        PatKind::Unit => "()".into(),
        PatKind::Con(n, args) if args.is_empty() => n.name.clone(),
        PatKind::Con(n, args) => {
            format!("({} {})", n.name, args.iter().map(pat).collect::<Vec<_>>().join(" "))
        }
        PatKind::Tuple(v) => format!("(tuple {})", v.iter().map(pat).collect::<Vec<_>>().join(" ")),
        PatKind::List(v) => format!("[{}]", v.iter().map(pat).collect::<Vec<_>>().join(" ")),
        PatKind::Cons(h, t) => format!("(:: {} {})", pat(h), pat(t)),
        PatKind::Or(v) => format!("(| {})", v.iter().map(pat).collect::<Vec<_>>().join(" ")),
    }
}
