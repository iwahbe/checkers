//! Classes and instances (D136). A class is desugared, before its module is
//! checked, into declarations the rest of the checker already knows:
//!
//! - a record of its functions (the *dictionary*), which only instances may
//!   build;
//! - for each function `f`, `fn f … : C a, …` reading it from the dictionary
//!   (its postconditions aren't checked there: each instance proves them);
//! - for each lemma, `lemma l … : C a, …`, assumed for every dictionary
//!   (each instance proves it).
//!
//! An instance `instance C (T a) : C2 a` becomes a function and a lemma per
//! member, with the class's signature at `T a`, and a function building the
//! dictionary from them. A clause `C t` in a signature is an implicit
//! parameter, the dictionary, which each use of the function gets by finding
//! the instance for `t`'s type (or a dictionary in scope).

use super::*;
use crate::syntax::ast::{Block, ClassMember, Constraint, Decl, DeclKind, Export, Expr, ExprKind, Ident, InstMember, PatKind, Pattern, Stmt};

/// Where a declaration of a desugared module came from.
#[derive(Clone, Debug, Default)]
pub enum Origin {
    #[default]
    Written,
    ClassRecord,
    /// A class's function, reading field `field` of the dictionary.
    ClassMethod,
    ClassLemma,
    /// The function building instance `inst`'s dictionary.
    InstDict(usize),
    /// A function or lemma of instance `inst`.
    InstMember(usize),
}

/// A class, as declared: what its instances must supply.
#[derive(Clone)]
pub struct ClassDef {
    pub module: String,
    pub name: String,
    pub param: String,
    pub members: Vec<ClassMember>,
    pub tid: TyId,
    pub span: Span,
}

/// A class's function gives a type for each parameter and its result
/// (else E0362, and instances leave it out).
fn fn_member_ok(m: &ClassMember) -> bool {
    match m {
        ClassMember::Fn { params, result, constraints, .. } => {
            let typed = |n: &str| constraints.iter().any(|c| matches!(c, Constraint::Typed { name, .. } if name.name == n));
            params.iter().all(|p| typed(&p.name)) && result.as_ref().is_some_and(|r| typed(&r.name))
        }
        ClassMember::Lemma { .. } | ClassMember::Type { .. } => true,
    }
}

impl ClassDef {
    pub fn methods(&self) -> Vec<String> {
        self.members.iter().filter_map(|m| if let ClassMember::Fn { name, .. } = m { Some(name.name.clone()) } else { None }).collect()
    }

    /// Its types' names (#133).
    pub fn types(&self) -> Vec<String> {
        type_names(&self.members)
    }
}

/// The names of a class's types (#133).
fn type_names(members: &[ClassMember]) -> Vec<String> {
    members.iter().filter_map(|m| if let ClassMember::Type { name, .. } = m { Some(name.name.clone()) } else { None }).collect()
}

/// Inside a class, its type `Name` is `C.Name a` (#133).
fn assoc_use(class: &str, param: &str, name: &str, s: Span) -> Expr {
    app(Expr { kind: ExprKind::Field(Box::new(con(class, s)), ident(name, s)), span: s }, var(param, s))
}

/// The dictionary's field holding the class's type `Name` (#133).
fn assoc_field_name(name: &str) -> String {
    format!("${name}")
}

/// The head of an instance's type.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum HeadKey {
    Ty(TyId),
    /// `()`, the tuple type of no parts.
    Unit,
    /// The pair: every tuple type is pairs, `(a, b, c)` being `(a, (b, c))`.
    Pair,
}

/// An instance, once registered.
#[derive(Clone)]
pub struct InstInfo {
    pub class: TyId,
    /// The function building its dictionary.
    pub def: DefId,
    pub module: String,
    pub span: Span,
    /// How many type variables its head has (`List a`: 1).
    pub n_vars: usize,
    /// Its context: a class and which of its variables (`Ord a`).
    pub context: Vec<(TyId, usize)>,
    /// Its members by name (functions and lemmas).
    pub members: HashMap<String, DefId>,
    /// As written: `Ord (List a)`.
    pub text: String,
}

/// An instance being desugared in this module (registered with its
/// dictionary function).
#[derive(Clone)]
pub struct PendingInst {
    pub class: Option<TyId>,
    pub class_name: String,
    pub head: Expr,
    pub vars: Vec<String>,
    pub context: Vec<(String, String)>,
    pub span: Span,
    pub text: String,
    pub members: Vec<(String, usize)>,
}

/// A dictionary to find once the types are known: the meta standing for it.
#[derive(Clone)]
pub struct InstReq {
    pub meta: Val,
    pub class: TyId,
    pub ty: Val,
    pub lvl: usize,
    pub names: Vec<Name>,
    pub span: Span,
    pub owner: Option<DefId>,
    pub in_spec: bool,
    /// Dictionaries in scope: level, class, type.
    pub given: Vec<(usize, TyId, Val)>,
    /// For a class's type, `C.Name` (#133): the dictionary is read for it.
    pub assoc: Option<String>,
}

/// `e` with every span `s`: code from another module, shown at `s`.
fn respan(e: &Expr, s: Span) -> Expr {
    let go = |x: &Expr| Box::new(respan(x, s));
    let id = |i: &Ident| Ident { name: i.name.clone(), span: s };
    let kind = match &e.kind {
        ExprKind::Tuple(xs) => ExprKind::Tuple(xs.iter().map(|x| respan(x, s)).collect()),
        ExprKind::List(xs) => ExprKind::List(xs.iter().map(|x| respan(x, s)).collect()),
        ExprKind::Par(xs) => ExprKind::Par(xs.iter().map(|x| respan(x, s)).collect()),
        ExprKind::App(a, b) => ExprKind::App(go(a), go(b)),
        ExprKind::Binary(op, a, b) => ExprKind::Binary(*op, go(a), go(b)),
        ExprKind::Arrow(a, b) => ExprKind::Arrow(go(a), go(b)),
        ExprKind::Index(a, b) => ExprKind::Index(go(a), go(b)),
        ExprKind::Neg(a) => ExprKind::Neg(go(a)),
        ExprKind::Try(a) => ExprKind::Try(go(a)),
        ExprKind::SectionL(op, a) => ExprKind::SectionL(*op, go(a)),
        ExprKind::SectionR(op, a) => ExprKind::SectionR(*op, go(a)),
        ExprKind::Field(a, f) => ExprKind::Field(go(a), id(f)),
        ExprKind::If(a, b, c) => ExprKind::If(go(a), go(b), go(c)),
        ExprKind::Lambda(ps, b) => ExprKind::Lambda(ps.clone(), go(b)),
        ExprKind::Match(x, arms) => ExprKind::Match(
            go(x),
            arms.iter()
                .map(|a| ast::Arm { pat: a.pat.clone(), guard: a.guard.as_ref().map(|g| respan(g, s)), body: respan(&a.body, s), span: s })
                .collect(),
        ),
        ExprKind::Refine(r) => ExprKind::Refine(Box::new(ast::RefineTy {
            param: r.param.as_ref().map(id),
            own: r.own,
            dom: respan(&r.dom, s),
            arrow: r.arrow.as_ref().map(|(n, t)| (n.as_ref().map(id), respan(t, s))),
            preds: r.preds.iter().map(|p| respan(p, s)).collect(),
        })),
        ExprKind::Forall(vs, cs) => ExprKind::Forall(vs.iter().map(id).collect(), respan_constraints(cs, s)),
        k => k.clone(),
    };
    Expr { kind, span: s }
}

fn respan_constraints(cs: &[Constraint], s: Span) -> Vec<Constraint> {
    cs.iter()
        .map(|c| match c {
            Constraint::Typed { name, mult, ty } => Constraint::Typed { name: Ident { name: name.name.clone(), span: s }, mult: *mult, ty: respan(ty, s) },
            Constraint::Pred(e) => Constraint::Pred(respan(e, s)),
            Constraint::Named(n, e) => Constraint::Named(Ident { name: n.name.clone(), span: s }, respan(e, s)),
        })
        .collect()
}

fn count(n: usize, what: &str) -> String {
    if n == 1 {
        format!("1 {what}")
    } else {
        format!("{n} {what}s")
    }
}

/// The most arguments `param` is applied to in `e` (its kind's arity, M25).
pub(crate) fn applied_arity(e: &Expr, param: &str) -> usize {
    let mut best = 0;
    fn go(e: &Expr, param: &str, best: &mut usize) {
        if let ExprKind::App(..) = &e.kind {
            let mut n = 0;
            let mut h = e;
            while let ExprKind::App(f, a) = &h.kind {
                go(a, param, best);
                n += 1;
                h = f;
            }
            if matches!(&h.kind, ExprKind::Var(v) if v == param) {
                *best = (*best).max(n);
            }
            return;
        }
        match &e.kind {
            ExprKind::Arrow(a, b) | ExprKind::Binary(_, a, b) => {
                go(a, param, best);
                go(b, param, best);
            }
            ExprKind::Tuple(xs) | ExprKind::List(xs) => xs.iter().for_each(|x| go(x, param, best)),
            ExprKind::Refine(r) => r.types().into_iter().for_each(|t| go(t, param, best)),
            _ => {}
        }
    }
    go(e, param, &mut best);
    best
}

/// The type variables of a class function's types other than the class's
/// own (`a` and `b` of `fn map g xs : g~(a -> b), xs~f a`), in order.
fn method_vars(tys: &[&Expr], param: &str, out: &mut Vec<String>) {
    fn go(e: &Expr, param: &str, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Var(v) if v != param && !out.contains(v) => out.push(v.clone()),
            ExprKind::App(a, b) | ExprKind::Arrow(a, b) | ExprKind::Binary(_, a, b) => {
                go(a, param, out);
                go(b, param, out);
            }
            ExprKind::Tuple(xs) | ExprKind::List(xs) => xs.iter().for_each(|x| go(x, param, out)),
            ExprKind::Refine(r) => r.types().into_iter().for_each(|t| go(t, param, out)),
            _ => {}
        }
    }
    for t in tys {
        go(t, param, out);
    }
}

/// The class function's own type variables that would be captured by the
/// instance's names (its parameters, or its type's variables), each given a
/// fresh name: `b` in `g~(a -> b)` when the instance names a parameter `b`.
fn hygiene(cs: &[Constraint], param: &str, taken: &[String]) -> HashMap<String, String> {
    let tys: Vec<&Expr> = cs
        .iter()
        .filter_map(|c| match c {
            Constraint::Typed { ty, .. } => Some(ty),
            _ => None,
        })
        .collect();
    let mut own = Vec::new();
    method_vars(&tys, param, &mut own);
    let mut map = HashMap::new();
    for v in own.iter().filter(|v| taken.contains(v)) {
        let mut k = 1;
        let fresh = loop {
            let n = format!("{v}{k}");
            if !taken.contains(&n) && !own.contains(&n) {
                break n;
            }
            k += 1;
        };
        map.insert(v.clone(), fresh);
    }
    map
}

fn ident(name: &str, span: Span) -> Ident {
    Ident { name: name.to_string(), span }
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

fn con(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Con(name.to_string()), span }
}

fn app(f: Expr, a: Expr) -> Expr {
    let span = f.span;
    Expr { kind: ExprKind::App(Box::new(f), Box::new(a)), span }
}

fn block(e: Expr) -> Block {
    let span = e.span;
    Block { stmts: Vec::new(), result: Box::new(e), span }
}

/// The names a pattern binds.
fn pat_binds(p: &Pattern, out: &mut Vec<String>) {
    match &p.kind {
        PatKind::Var(n) => out.push(n.clone()),
        PatKind::Con(_, ps) | PatKind::Tuple(ps) | PatKind::List(ps) | PatKind::Or(ps) => ps.iter().for_each(|q| pat_binds(q, out)),
        PatKind::Cons(a, b) => {
            pat_binds(a, out);
            pat_binds(b, out);
        }
        PatKind::Record(_, fs) => fs.iter().for_each(|(_, q)| pat_binds(q, out)),
        _ => {}
    }
}

/// A rewrite of the free names of an expression: `Var`s, `Con`s and
/// qualified names (`m.x`), respecting what lambdas, `match`, `let` and
/// `forall` bind.
struct Rewrite<'a> {
    var: &'a dyn Fn(&str, Span) -> Option<Expr>,
    con: &'a dyn Fn(&str, Span) -> Option<Expr>,
    qualified: &'a dyn Fn(&str, &str, Span) -> Option<Expr>,
}

impl Rewrite<'_> {
    fn expr(&self, e: &Expr, bound: &[String]) -> Expr {
        let go = |x: &Expr| Box::new(self.expr(x, bound));
        let kind = match &e.kind {
            ExprKind::Var(n) if !bound.contains(n) => match (self.var)(n, e.span) {
                Some(r) => return r,
                None => e.kind.clone(),
            },
            ExprKind::Con(n) => match (self.con)(n, e.span) {
                Some(r) => return r,
                None => e.kind.clone(),
            },
            ExprKind::Field(x, f) => {
                if let ExprKind::Var(q) = &x.kind {
                    if !bound.contains(q) {
                        if let Some(r) = (self.qualified)(q, &f.name, e.span) {
                            return r;
                        }
                    }
                }
                ExprKind::Field(go(x), f.clone())
            }
            ExprKind::Tuple(xs) => ExprKind::Tuple(xs.iter().map(|x| self.expr(x, bound)).collect()),
            ExprKind::List(xs) => ExprKind::List(xs.iter().map(|x| self.expr(x, bound)).collect()),
            ExprKind::Par(xs) => ExprKind::Par(xs.iter().map(|x| self.expr(x, bound)).collect()),
            ExprKind::App(a, b) => ExprKind::App(go(a), go(b)),
            ExprKind::Binary(op, a, b) => ExprKind::Binary(*op, go(a), go(b)),
            ExprKind::Arrow(a, b) => ExprKind::Arrow(go(a), go(b)),
            ExprKind::Index(a, b) => ExprKind::Index(go(a), go(b)),
            ExprKind::Neg(a) => ExprKind::Neg(go(a)),
            ExprKind::SectionL(op, a) => ExprKind::SectionL(*op, go(a)),
            ExprKind::SectionR(op, a) => ExprKind::SectionR(*op, go(a)),
            ExprKind::Try(a) => ExprKind::Try(go(a)),
            ExprKind::If(a, b, c) => ExprKind::If(go(a), go(b), go(c)),
            ExprKind::Match(s, arms) => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let mut b = bound.to_vec();
                        pat_binds(&arm.pat, &mut b);
                        ast::Arm {
                            pat: self.pat(&arm.pat),
                            guard: arm.guard.as_ref().map(|g| self.expr(g, &b)),
                            body: self.expr(&arm.body, &b),
                            span: arm.span,
                        }
                    })
                    .collect();
                ExprKind::Match(go(s), arms)
            }
            ExprKind::Lambda(ps, body) => {
                let mut b = bound.to_vec();
                ps.iter().for_each(|p| pat_binds(p, &mut b));
                ExprKind::Lambda(ps.iter().map(|p| self.pat(p)).collect(), Box::new(self.expr(body, &b)))
            }
            ExprKind::Refine(r) => {
                let mut b = bound.to_vec();
                b.extend(r.binders());
                ExprKind::Refine(Box::new(ast::RefineTy {
                    param: r.param.clone(),
                    own: r.own,
                    dom: self.expr(&r.dom, bound),
                    arrow: r.arrow.as_ref().map(|(n, t)| (n.clone(), self.expr(t, &b))),
                    preds: r.preds.iter().map(|p| self.expr(p, &b)).collect(),
                }))
            }
            ExprKind::Forall(vs, cs) => {
                let mut b = bound.to_vec();
                b.extend(vs.iter().map(|v| v.name.clone()));
                ExprKind::Forall(vs.clone(), self.constraints(cs, &b))
            }
            ExprKind::Block(blk) => ExprKind::Block(self.block(blk, bound)),
            _ => e.kind.clone(),
        };
        Expr { kind, span: e.span }
    }

    fn pat(&self, p: &Pattern) -> Pattern {
        let kind = match &p.kind {
            PatKind::Con(c, ps) => {
                let c = match (self.con)(&c.name, c.span) {
                    Some(Expr { kind: ExprKind::Con(n), .. }) => Ident { name: n, span: c.span },
                    _ => c.clone(),
                };
                PatKind::Con(c, ps.iter().map(|q| self.pat(q)).collect())
            }
            PatKind::Tuple(ps) => PatKind::Tuple(ps.iter().map(|q| self.pat(q)).collect()),
            PatKind::List(ps) => PatKind::List(ps.iter().map(|q| self.pat(q)).collect()),
            PatKind::Or(ps) => PatKind::Or(ps.iter().map(|q| self.pat(q)).collect()),
            PatKind::Cons(a, b) => PatKind::Cons(Box::new(self.pat(a)), Box::new(self.pat(b))),
            k => k.clone(),
        };
        Pattern { kind, span: p.span }
    }

    fn block(&self, blk: &Block, bound: &[String]) -> Block {
        let mut b = bound.to_vec();
        let mut stmts = Vec::new();
        for s in &blk.stmts {
            stmts.push(match s {
                Stmt::Let(p, e) => {
                    let e = self.expr(e, &b);
                    pat_binds(p, &mut b);
                    Stmt::Let(self.pat(p), e)
                }
                Stmt::Have(e) => Stmt::Have(self.expr(e, &b)),
                Stmt::HaveType(x, t) => Stmt::HaveType(x.clone(), self.expr(t, &b)),
                Stmt::Expr(e) => Stmt::Expr(self.expr(e, &b)),
                Stmt::When(w) => Stmt::When(w.clone()),
            });
        }
        Block { stmts, result: Box::new(self.expr(&blk.result, &b)), span: blk.span }
    }

    fn constraints(&self, cs: &[Constraint], bound: &[String]) -> Vec<Constraint> {
        cs.iter()
            .map(|c| match c {
                Constraint::Typed { name, mult, ty } => Constraint::Typed { name: name.clone(), mult: *mult, ty: self.expr(ty, bound) },
                Constraint::Pred(e) => Constraint::Pred(self.expr(e, bound)),
                Constraint::Named(n, e) => Constraint::Named(n.clone(), self.expr(e, bound)),
            })
            .collect()
    }
}

/// Rename the names a signature binds (its parameters) in its constraints.
/// Free variables renamed (binders kept).
fn rename_vars(cs: &[Constraint], map: &HashMap<String, String>) -> Vec<Constraint> {
    if map.is_empty() {
        return cs.to_vec();
    }
    let f = |n: &str, s: Span| map.get(n).map(|m| var(m, s));
    let none = |_: &str, _: Span| None;
    let nq = |_: &str, _: &str, _: Span| None;
    let rw = Rewrite { var: &f, con: &none, qualified: &nq };
    rw.constraints(cs, &[])
}

fn rename_binders(cs: &[Constraint], map: &HashMap<String, String>) -> Vec<Constraint> {
    let f = |n: &str, s: Span| map.get(n).map(|m| var(m, s));
    let none = |_: &str, _: Span| None;
    let nq = |_: &str, _: &str, _: Span| None;
    let rw = Rewrite { var: &f, con: &none, qualified: &nq };
    rw.constraints(cs, &[])
        .into_iter()
        .map(|c| match c {
            Constraint::Typed { name, mult, ty } => {
                let name = map.get(&name.name).map(|m| ident(m, name.span)).unwrap_or(name);
                Constraint::Typed { name, mult, ty }
            }
            c => c,
        })
        .collect()
}

impl Elab {
    /// Is `e` a class clause (`Ord a`)? The class, if so.
    pub fn class_clause(&self, e: &Expr) -> Option<TyId> {
        let ExprKind::App(f, _) = &e.kind else { return None };
        let ExprKind::Con(n) = &f.kind else { return None };
        match self.resolve(n, true) {
            Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => Some(t),
            _ => None,
        }
    }

    /// The symbol a generated name stands for: `$sym#D12` (a definition),
    /// `$sym#T3` (a type), `$sym#C4` (a constructor), or `$mk#mod.Name`
    /// (the constructor of class `Name`'s dictionary).
    pub fn generated_sym(&self, name: &str) -> Option<Sym> {
        if let Some(rest) = name.strip_prefix("$sym#") {
            let (k, n) = rest.split_at(1);
            let n: u32 = n.parse().ok()?;
            return Some(match k {
                "D" => Sym::Def(DefId(n)),
                "T" => Sym::Ty(TyId(n)),
                "C" => Sym::Con(ConId(n)),
                "U" => Sym::Univ,
                _ => return None,
            });
        }
        if let Some(rest) = name.strip_prefix("$mk#") {
            let tid = self.class_defs.values().find(|c| format!("{}.{}", c.module, c.name) == rest)?.tid;
            return Some(Sym::Con(self.g.tys[tid.0 as usize].ctors[0]));
        }
        None
    }

    fn sym_name(s: Sym) -> String {
        match s {
            Sym::Def(d) => format!("$sym#D{}", d.0),
            Sym::Ty(t) => format!("$sym#T{}", t.0),
            Sym::Con(c) => format!("$sym#C{}", c.0),
            Sym::Univ => "$sym#U0".into(),
            Sym::Len => "len".into(),
            Sym::Format => "format".into(),
        }
    }

    /// The members of a class declared in another module, with every name
    /// they use from that module resolved there (so they mean the same in
    /// the instance's module).
    fn members_for_instance(&self, c: &ClassDef) -> Vec<ClassMember> {
        if c.module == self.cur {
            return c.members.clone();
        }
        let Some(mi) = self.modules.get(&c.module) else { return c.members.clone() };
        let lookup = |n: &str, type_pos: bool| -> Option<Sym> {
            let firsts = if type_pos { [&mi.types, &mi.import_types] } else { [&mi.values, &mi.import_values] };
            let seconds = if type_pos { [&mi.values, &mi.import_values] } else { [&mi.types, &mi.import_types] };
            firsts.into_iter().chain(seconds).find_map(|m| m.get(n).copied())
        };
        let v = |n: &str, s: Span| -> Option<Expr> {
            let sym = lookup(n, false)?;
            Some(var(&Self::sym_name(sym), s))
        };
        // The class's own types stay by name: each instance gives them.
        let tnames = c.types();
        let k = |n: &str, s: Span| -> Option<Expr> {
            if tnames.iter().any(|t| t == n) {
                return None;
            }
            let sym = lookup(n, true)?;
            Some(con(&Self::sym_name(sym), s))
        };
        let q = |q: &str, n: &str, s: Span| -> Option<Expr> {
            let m = mi.qualifiers.get(q)?;
            let sym = self.resolve_qualified(m, n, false)?;
            Some(var(&Self::sym_name(sym), s))
        };
        let rw = Rewrite { var: &v, con: &k, qualified: &q };
        c.members
            .iter()
            .map(|m| match m {
                ClassMember::Type { name, default, span } => {
                    ClassMember::Type { name: name.clone(), default: default.as_ref().map(|e| rw.expr(e, &[])), span: *span }
                }
                ClassMember::Fn { name, params, result, constraints, span } => {
                    let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                    bound.extend(result.iter().map(|r| r.name.clone()));
                    ClassMember::Fn {
                        name: name.clone(),
                        params: params.clone(),
                        result: result.clone(),
                        constraints: rw.constraints(constraints, &bound),
                        span: *span,
                    }
                }
                ClassMember::Lemma { name, params, constraints, lets, ensures, span } => {
                    let mut bound: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                    let constraints = rw.constraints(constraints, &bound);
                    let mut ls = Vec::new();
                    for (p, e) in lets {
                        ls.push((p.clone(), rw.expr(e, &bound)));
                        pat_binds(p, &mut bound);
                    }
                    ClassMember::Lemma { name: name.clone(), params: params.clone(), constraints, lets: ls, ensures: rw.expr(ensures, &bound), span: *span }
                }
            })
            .collect()
    }

    /// A span of its own, for a text override, shown at `at` (D136): past
    /// the end of the file, so it never collides with real code.
    fn synthetic_span(&mut self, at: Span) -> Span {
        let start = SYNTHETIC + self.synthetic.len() as u32;
        self.synthetic.insert((self.cur.clone(), start), at);
        Span { start, end: start + 1 }
    }

    /// The real span of `span` in module `m`: a synthetic one's anchor.
    pub fn real_span(&self, m: &str, span: Span) -> Span {
        if span.start < SYNTHETIC {
            return span;
        }
        self.synthetic.get(&(m.to_string(), span.start)).copied().unwrap_or(Span { start: 0, end: 0 })
    }

    /// Source text of `span` in module `m`.
    fn text_in(&self, m: &str, span: Span) -> String {
        self.sources
            .get(m)
            .and_then(|f| f.text.get(span.start as usize..span.end as usize))
            .map(|t| t.split_whitespace().collect::<Vec<_>>().join(" "))
            .unwrap_or_default()
    }

    /// A class's constraints for an instance member in another module:
    /// each shown at the member (`at`), with its own text.
    fn shown_here(&mut self, foreign: Option<&str>, original: &[Constraint], cs: Vec<Constraint>, at: Span) -> Vec<Constraint> {
        let Some(m) = foreign else { return cs };
        cs.iter()
            .zip(original)
            .enumerate()
            .map(|(k, (c, o))| {
                // A distinct span for each, within the member's.
                let _ = k;
                let s = self.synthetic_span(at);
                let oe = match o {
                    Constraint::Typed { ty, .. } => ty.span,
                    Constraint::Pred(e) | Constraint::Named(_, e) => e.span,
                };
                let text = self.text_in(m, oe);
                self.text_override.insert((self.cur.clone(), s.start, s.end), text);
                respan_constraints(std::slice::from_ref(c), s).remove(0)
            })
            .collect()
    }

    /// Desugar the module's classes and instances (D136). Returns the new
    /// module and where each of its declarations came from.
    pub fn desugar_classes(&mut self, m: &ast::Module) -> (ast::Module, Vec<Origin>) {
        let has = m.decls.iter().any(|d| matches!(d.kind, DeclKind::Class { .. } | DeclKind::Instance { .. }));
        if !has {
            return (m.clone(), vec![Origin::Written; m.decls.len()]);
        }
        let mut decls = Vec::new();
        let mut origins = Vec::new();
        let local: HashMap<String, (String, Vec<ClassMember>, Span)> = m
            .decls
            .iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Class { name, param, members } => Some((name.name.clone(), (param.name.clone(), members.clone(), name.span))),
                _ => None,
            })
            .collect();
        self.local_ty_params = m
            .decls
            .iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Enum { name, params, .. } | DeclKind::Record { name, params, .. } => Some((name.name.clone(), params.len())),
                _ => None,
            })
            .collect();
        self.local_names = m
            .decls
            .iter()
            .flat_map(|d| match &d.kind {
                DeclKind::Enum { name, ctors, .. } => std::iter::once(name).chain(ctors.iter().map(|c| &c.name)).map(|n| (n.name.clone(), false)).collect(),
                DeclKind::Alias { name, .. } => vec![(name.name.clone(), true)],
                DeclKind::Fn { name, .. }
                | DeclKind::Record { name, .. }
                | DeclKind::Lemma { name, .. }
                | DeclKind::Const { name, .. }
                | DeclKind::Class { name, .. } => vec![(name.name.clone(), false)],
                DeclKind::Check { .. } | DeclKind::Instance { .. } => vec![],
            })
            .collect();
        for d in &m.decls {
            match &d.kind {
                DeclKind::Class { name, param, members } => self.desugar_class(d, name, param, members, &mut decls, &mut origins),
                DeclKind::Instance { class, ty, context, members } => {
                    self.desugar_instance(d, class, ty, context, members, &local, &mut decls, &mut origins)
                }
                _ => {
                    decls.push(d.clone());
                    origins.push(Origin::Written);
                }
            }
        }
        (ast::Module { name: m.name.clone(), imports: m.imports.clone(), decls }, origins)
    }

    fn desugar_class(&mut self, d: &Decl, name: &Ident, param: &Ident, members: &[ClassMember], decls: &mut Vec<Decl>, origins: &mut Vec<Origin>) {
        let sp = name.span;
        let clause = app(con(&name.name, sp), var(&param.name, sp));
        let mut fields = Vec::new();
        let mut type_fields = Vec::new();
        let mut seen = HashSet::new();
        // Its types (#133): in the dictionary, a field of its own; in its
        // functions' and lemmas' signatures, `C.Name a`.
        let tnames = type_names(members);
        let to_field = |n: &str, s: Span| if tnames.iter().any(|t| t == n) { Some(var(&assoc_field_name(n), s)) } else { None };
        let (cname, pname) = (name.name.clone(), param.name.clone());
        let to_assoc = |n: &str, s: Span| if tnames.iter().any(|t| t == n) { Some(assoc_use(&cname, &pname, n, s)) } else { None };
        let none = |_: &str, _: Span| None;
        let nq = |_: &str, _: &str, _: Span| None;
        let frw = Rewrite { var: &none, con: &to_field, qualified: &nq };
        let arw = Rewrite { var: &none, con: &to_assoc, qualified: &nq };
        for mem in members {
            let (mname, mspan) = (mem.name(), mem.span());
            if !seen.insert(mname.name.clone()) {
                self.err(Diagnostic::error("E0350", format!("`{}` is defined twice in class `{}`", mname.name, name.name), mname.span));
                continue;
            }
            match mem {
                ClassMember::Type { name: t, default, .. } => {
                    if let Some(e) = default.as_ref().filter(|e| super::decls::mentions_free(e, &param.name)) {
                        self.err(
                            Diagnostic::error("E0288", format!("the default of `{}` can't mention the class's parameter `{}`", t.name, param.name), e.span)
                                .with_help(format!("a default is the same type at every instance; an instance that needs `{}` gives `type {} = …` itself", param.name, t.name)),
                        );
                    }
                    type_fields.push(ast::Field {
                        name: ident(&assoc_field_name(&t.name), t.span),
                        mult: ast::Mult::Ghost,
                        ty: con("Type", t.span),
                        preds: Vec::new(),
                        span: mspan,
                    });
                }
                ClassMember::Fn { name: f, params, result, constraints, .. } => {
                    // The dictionary's field: the function's type, without refinements' predicates.
                    let typed = |n: &str| {
                        constraints.iter().find_map(|c| match c {
                            Constraint::Typed { name, ty, .. } if name.name == n => Some(ty.clone()),
                            _ => None,
                        })
                    };
                    let mut missing = Vec::new();
                    let mut tys = Vec::new();
                    for p in params {
                        match typed(&p.name) {
                            Some(t) => tys.push(t),
                            None => missing.push(p.name.clone()),
                        }
                    }
                    let rty = match result.as_ref().and_then(|r| typed(&r.name)) {
                        Some(t) => Some(t),
                        None => {
                            missing.push(result.as_ref().map(|r| r.name.clone()).unwrap_or_else(|| "its result".into()));
                            None
                        }
                    };
                    if !missing.is_empty() || rty.is_none() {
                        self.err(
                            Diagnostic::error("E0362", format!("class function `{}` must give the type of each parameter and of its result", f.name), f.span)
                                .with_label(format!("no type for `{}`", missing.join("`, `")))
                                .with_help("write `-> r` and a type for each name, e.g. `fn le x y -> r : x~a, y~a, r~Bool`"),
                        );
                        continue;
                    }
                    let rty = rty.unwrap();
                    // Each parameter's `own` or `ghost` (D156 i): the field's type takes it the same way.
                    let mults: Vec<Mult> = params
                        .iter()
                        .map(|p| {
                            let m = constraints.iter().find_map(|c| match c {
                                Constraint::Typed { name, mult, .. } if name.name == p.name => Some(*mult),
                                _ => None,
                            });
                            Self::mult_of(m.unwrap_or(ast::Mult::Many))
                        })
                        .collect();
                    if mults.iter().any(|m| *m != Mult::Many) {
                        self.class_mults.insert(format!("{}.{}.{}", self.cur, name.name, f.name), mults);
                    }
                    // Its own type variables make the field polymorphic: an
                    // implicit, erased parameter of type `Type` each (M25).
                    let mut own = Vec::new();
                    let refs: Vec<&Expr> = tys.iter().chain(std::iter::once(&rty)).collect();
                    method_vars(&refs, &param.name, &mut own);
                    let ren: HashMap<String, String> = own.iter().map(|v| (v.clone(), format!("'{v}"))).collect();
                    let to_q = |n: &str, s: Span| ren.get(n).map(|m| var(m, s));
                    let none = |_: &str, _: Span| None;
                    let nq = |_: &str, _: &str, _: Span| None;
                    let qrw = Rewrite { var: &to_q, con: &none, qualified: &nq };
                    let mut fty = qrw.expr(&frw.expr(&rty, &[]), &[]);
                    for t in tys.into_iter().rev() {
                        let span = t.span;
                        fty = Expr { kind: ExprKind::Arrow(Box::new(qrw.expr(&frw.expr(&t, &[]), &[])), Box::new(fty)), span };
                    }
                    for v in own.iter().rev() {
                        let span = fty.span;
                        fty = Expr {
                            kind: ExprKind::Refine(Box::new(ast::RefineTy {
                                param: Some(ident(&format!("'{v}"), span)),
                                own: false,
                                dom: con("Type", span),
                                arrow: Some((None, fty)),
                                preds: Vec::new(),
                            })),
                            span,
                        };
                    }
                    fields.push(ast::Field { name: f.clone(), mult: ast::Mult::Many, ty: fty, preds: Vec::new(), span: mspan });
                    // The function reading it (its body placed after its
                    // header, which is then its whole text, for hover).
                    let at_end = Span { start: mspan.end, end: mspan.end };
                    let mut call = Expr { kind: ExprKind::Field(Box::new(var("$d0", at_end)), Ident { name: f.name.clone(), span: at_end }), span: at_end };
                    for p in params {
                        call = app(call, var(&p.name, at_end));
                    }
                    let mut cs = vec![Constraint::Pred(clause.clone())];
                    cs.extend(arw.constraints(constraints, &[]));
                    decls.push(Decl {
                        export: if d.export == Export::No { Export::No } else { Export::Transparent },
                        kind: DeclKind::Fn {
                            partial: false,
                            name: f.clone(),
                            params: params.clone(),
                            result: result.clone(),
                            constraints: cs,
                            decreasing: None,
                            body: block(call),
                        },
                        span: mspan,
                    });
                    origins.push(Origin::ClassMethod);
                }
                ClassMember::Lemma { name: l, params, constraints, lets, ensures, .. } => {
                    let mut cs = vec![Constraint::Pred(clause.clone())];
                    cs.extend(arw.constraints(constraints, &[]));
                    decls.push(Decl {
                        export: if d.export == Export::No { Export::No } else { Export::Yes },
                        kind: DeclKind::Lemma {
                            name: l.clone(),
                            params: params.clone(),
                            constraints: cs,
                            decreasing: None,
                            lets: lets.iter().map(|(p, e)| (p.clone(), arw.expr(e, &[]))).collect(),
                            ensures: arw.expr(ensures, &[]),
                            proof: Some(block(var("__class_lemma", l.span))),
                        },
                        span: mspan,
                    });
                    origins.push(Origin::ClassLemma);
                }
            }
        }
        // The parameter's kind: `Type`, or `Type -> Type` if the members
        // apply it to one argument, and so on (M25).
        let mut arity = 0;
        for mem in members {
            let cs = match mem {
                ClassMember::Fn { constraints, .. } | ClassMember::Lemma { constraints, .. } => constraints,
                ClassMember::Type { .. } => continue,
            };
            for c in cs {
                if let Constraint::Typed { ty, .. } = c {
                    arity = arity.max(applied_arity(ty, &param.name));
                }
            }
        }
        let mut kind = con("Type", sp);
        for _ in 0..arity {
            kind = Expr { kind: ExprKind::Arrow(Box::new(con("Type", sp)), Box::new(kind)), span: sp };
        }
        let rcs = if arity == 0 { Vec::new() } else { vec![Constraint::Typed { name: param.clone(), mult: ast::Mult::Many, ty: kind }] };
        decls.push(Decl {
            export: if d.export == Export::No { Export::No } else { Export::Abstract },
            kind: DeclKind::Record {
                name: name.clone(),
                params: vec![ast::Param { polarity: None, name: param.clone() }],
                constraints: rcs,
                fields: type_fields.into_iter().chain(fields).collect(),
            },
            span: d.span,
        });
        origins.push(Origin::ClassRecord);
        self.pending_classes.push((name.name.clone(), param.name.clone(), members.to_vec(), name.span));
    }

    /// Whether an instance's head is the unit type: `()`, or an alias of it
    /// declared elsewhere (the prelude's `Unit`).
    fn is_unit_head(&self, ty: &Expr) -> bool {
        match &ty.kind {
            ExprKind::Unit => true,
            ExprKind::Tuple(xs) => xs.is_empty(),
            ExprKind::Con(n) if !self.local_ty_params.contains_key(n) && !self.local_names.contains_key(n) => match self.resolve(n, true) {
                Some(Sym::Def(d)) => matches!(&self.g.defs[d.0 as usize].body, Some(Tm::TupleTy(xs)) if xs.is_empty()),
                _ => false,
            },
            _ => false,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn desugar_instance(
        &mut self,
        d: &Decl,
        class: &Ident,
        ty: &Expr,
        context: &[Expr],
        members: &[InstMember],
        local: &HashMap<String, (String, Vec<ClassMember>, Span)>,
        decls: &mut Vec<Decl>,
        origins: &mut Vec<Origin>,
    ) {
        let text = format!("{} {}", class.name, self.src_text(ty.span).trim());
        // The class: declared here, or imported.
        let (param, cmembers, class_tid) = match local.get(&class.name) {
            Some((p, ms, _)) => (p.clone(), ms.clone(), None),
            None => match self.resolve(&class.name, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => {
                    let c = self.class_defs[&t].clone();
                    (c.param.clone(), self.members_for_instance(&c), Some(t))
                }
                _ => {
                    self.err(
                        Diagnostic::error("E0280", format!("`{}` is not a class", class.name), class.span)
                            .with_help("an instance is of a class declared with `class`"),
                    );
                    return;
                }
            },
        };
        // `()`, written so or as the prelude's `Unit`: the tuple type of no
        // elements, a type constructor with no parameters.
        let unit_head = Expr { kind: ExprKind::Tuple(Vec::new()), span: ty.span };
        let head_ty = if self.is_unit_head(ty) { &unit_head } else { ty };
        // The head: a type constructor applied to distinct type variables.
        let mut args = Vec::new();
        let mut h = head_ty;
        while let ExprKind::App(f, a) = &h.kind {
            args.push((**a).clone());
            h = f;
        }
        args.reverse();
        let mut vars: Vec<String> = Vec::new();
        let ok = match &h.kind {
            ExprKind::Con(_) => args.iter().all(|a| matches!(&a.kind, ExprKind::Var(v) if !vars.contains(v) && { vars.push(v.clone()); true })),
            ExprKind::Tuple(xs) if args.is_empty() && matches!(xs.len(), 0 | 2) => xs.iter().all(|a| matches!(&a.kind, ExprKind::Var(v) if !vars.contains(v) && { vars.push(v.clone()); true })),
            _ => false,
        };
        match &h.kind {
            ExprKind::Tuple(xs) if args.is_empty() && xs.len() > 2 => {
                let part = |x: &Expr| self.src_text(x.span).trim().to_string();
                let rest: Vec<String> = xs[1..].iter().map(part).collect();
                self.err(
                    Diagnostic::error("E0281", format!("`instance {text}` must be for a pair"), ty.span)
                        .with_label(format!("this is `({}, ({}))`", part(&xs[0]), rest.join(", ")))
                        .with_help(format!(
                            "write `instance {} (a, b)`: it covers every tuple of two or more parts, `b` being the rest",
                            class.name
                        )),
                );
                return;
            }
            _ => {}
        }
        if !ok {
            self.err(
                Diagnostic::error("E0281", format!("`instance {text}` must be for a type applied to distinct type variables"), ty.span)
                    .with_label("not a type constructor applied to variables")
                    .with_help("write it for every element type, e.g. `instance Ord (List a) : Ord a`"),
            );
            return;
        }
        // Its kind: a class over types of `n` parameters (M25) takes a type
        // constructor short of `n` arguments.
        let want = cmembers
            .iter()
            .flat_map(|m| match m {
                ClassMember::Fn { constraints, .. } | ClassMember::Lemma { constraints, .. } => constraints.as_slice(),
                ClassMember::Type { .. } => &[],
            })
            .filter_map(|c| match c {
                Constraint::Typed { ty, .. } => Some(applied_arity(ty, &param)),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        // This module's names aren't registered yet: its types are in
        // `local_ty_params`, its other names in `local_names`.
        let alias = |n: &str| match self.local_names.get(n) {
            Some(is_alias) => *is_alias,
            None => matches!(self.resolve(n, true), Some(Sym::Def(_))),
        };
        let have = match &h.kind {
            ExprKind::Con(n) if !self.local_ty_params.contains_key(n) && alias(n) => {
                self.err(
                    Diagnostic::error("E0281", format!("`instance {text}` is for a type alias"), ty.span)
                        .with_help("write the instance for the type the alias stands for; it applies to the alias too"),
                );
                return;
            }
            ExprKind::Con(n) => match self.local_ty_params.get(n) {
                Some(k) => Some(*k),
                None => match self.resolve(n, true) {
                    Some(Sym::Ty(t)) => Some(self.g.tys[t.0 as usize].params.len()),
                    // An unknown type: nothing of the instance can be checked.
                    None if !self.local_names.contains_key(n) => {
                        let mut e = Diagnostic::error("E0204", format!("unknown name `{n}`"), h.span).with_label("not found");
                        if let Some(m) = self.private_in_imports(n) {
                            e = e.with_help(Self::private_help(&m, n));
                        }
                        self.err(e);
                        return;
                    }
                    // A class declared here: its kind is checked later.
                    _ if local.contains_key(n) => None,
                    // `Type`, a constructor, a value: not a type, so nothing
                    // of the instance can be checked.
                    s => {
                        let label = if matches!(s, Some(Sym::Univ)) { "the type of types, not a type" } else { "not a type" };
                        self.err(
                            Diagnostic::error("E0281", format!("`instance {text}` must be for a type"), h.span)
                                .with_label(label)
                                .with_help("an instance is for a type constructor applied to distinct type variables, e.g. `instance Ord (List a) : Ord a`"),
                        );
                        return;
                    }
                },
            },
            _ => Some(args.len()),
        };
        if let Some(k) = have.filter(|k| k.checked_sub(args.len()) != Some(want)) {
            let shown = |n: usize| match n {
                0 => "a type, like `Int`".to_string(),
                1 => "a type constructor of one parameter, like `List`".to_string(),
                n => format!("a type constructor of {n} parameters"),
            };
            let plain = |n: usize| match n {
                0 => "a type".to_string(),
                1 => "a type constructor of one parameter".to_string(),
                n => format!("a type constructor of {n} parameters"),
            };
            let given = k.saturating_sub(args.len());
            let fix = if want == 0 {
                let vs: Vec<String> = (0..given).map(|i| ((b'a' + (i % 26) as u8) as char).to_string()).collect();
                format!("give it its parameters, as in `instance {} ({} {})`", class.name, self.src_text(ty.span).trim(), vs.join(" "))
            } else if want < given {
                "leave the last parameters off; the class's functions supply them".to_string()
            } else {
                format!("`{}` is for a type that takes its element type as its last parameter, like `List` or `Option`", class.name)
            };
            self.err(
                Diagnostic::error("E0286", format!("`{}` is for {}, but `{}` is {}", class.name, shown(want), self.src_text(ty.span).trim(), plain(given)), ty.span)
                    .with_help(fix),
            );
            return;
        }
        // Its context: classes of its variables.
        let mut ctx = Vec::new();
        for c in context {
            let good = match &c.kind {
                ExprKind::App(f, a) => match (&f.kind, &a.kind) {
                    (ExprKind::Con(cn), ExprKind::Var(v)) if vars.contains(v) => {
                        ctx.push((cn.clone(), v.clone()));
                        true
                    }
                    _ => false,
                },
                _ => false,
            };
            if !good {
                self.err(
                    Diagnostic::error("E0281", "an instance's context is classes of its type's variables", c.span)
                        .with_help("write e.g. `instance Ord (List a) : Ord a`"),
                );
                return;
            }
        }
        let ctx_preds: Vec<Constraint> = context.iter().map(|c| Constraint::Pred(c.clone())).collect();
        // A class from another module: its code is shown at the instance.
        let foreign: Option<String> = class_tid.map(|t| self.class_defs[&t].module.clone()).filter(|m| *m != self.cur);
        let all_members = cmembers.clone();
        let cmembers: Vec<ClassMember> = cmembers.into_iter().filter(fn_member_ok).collect();
        // Two instances here for the same class and type (one elsewhere is
        // found when it is registered).
        let head_name = match &h.kind {
            ExprKind::Con(n) => n.clone(),
            _ => format!("tuple{}", vars.len()),
        };
        if let Some(prev) = self.pending_insts.iter().find(|p| {
            let mut ph = &p.head;
            while let ExprKind::App(f, _) = &ph.kind {
                ph = f;
            }
            let pn = match &ph.kind {
                ExprKind::Con(n) => n.clone(),
                _ => format!("tuple{}", p.vars.len()),
            };
            p.class_name == class.name && pn == head_name
        }) {
            let line = self.sources.get(&self.cur).map(|f| f.line_col(prev.span.start).0).unwrap_or(0);
            let prev_text = prev.text.clone();
            self.err(
                Diagnostic::error("E0283", format!("`instance {text}` overlaps another instance"), d.span)
                    .with_label(format!("`{prev_text}` is already declared on line {line}"))
                    .with_help("a type has one instance of each class; give the other order through a wrapper type, or `sort_as`/`sort_by`"),
            );
            return;
        }
        let inst_ix = self.pending_insts.len();
        let mut head_vars = Vec::new();
        method_vars(&[ty], "", &mut head_vars);
        let gen = |n: &str| format!("{text}.{n}");
        // Each member's name in this instance.
        let mut rename: HashMap<String, String> = HashMap::new();
        for m in members {
            if let InstMember::Fn { name, .. } | InstMember::Lemma { name, .. } = m {
                rename.insert(name.name.clone(), gen(&name.name));
            }
        }
        let cnames: Vec<String> = cmembers.iter().map(|m| m.name().name.clone()).collect();
        let kind_of = |m: &ClassMember| match m {
            ClassMember::Type { .. } => "type",
            ClassMember::Fn { .. } => "function",
            ClassMember::Lemma { .. } => "lemma",
        };
        let mut bad = false;
        for m in members {
            let n = m.name();
            let span = n.span;
            let what = match m {
                InstMember::Type { .. } => "type",
                InstMember::Fn { .. } => "function",
                InstMember::Lemma { .. } => "lemma",
            };
            let class_kind = all_members.iter().find(|cm| cm.name().name == n.name).map(kind_of);
            if class_kind != Some(what) {
                self.err(
                    Diagnostic::error("E0363", format!("class `{}` has no {what} `{}`", class.name, n.name), span)
                        .with_help(format!("its members are `{}`", cnames.join("`, `"))),
                );
                bad = true;
            }
        }
        // The class's types at this instance (#133): given, or the class's
        // default (written in the class, so shown at the instance's header).
        let header = Span { start: d.span.start, end: ty.span.end };
        let mut types: Vec<(String, Expr)> = Vec::new();
        for cm in &all_members {
            let ClassMember::Type { name: tn, default, .. } = cm else { continue };
            let given = members.iter().find_map(|m| match m {
                InstMember::Type { name, ty, .. } if name.name == tn.name => Some(ty.clone()),
                _ => None,
            });
            let t = match (given, default) {
                (Some(t), _) => t,
                (None, Some(dflt)) => match foreign.as_deref() {
                    Some(m) => {
                        let at = self.synthetic_span(header);
                        let text = self.text_in(m, dflt.span);
                        self.text_override.insert((self.cur.clone(), at.start, at.end), text);
                        respan(dflt, at)
                    }
                    None => dflt.clone(),
                },
                (None, None) => {
                    self.err(
                        Diagnostic::error("E0364", format!("`instance {text}` doesn't give `{}`", tn.name), d.span)
                            .with_label(format!("`{}` missing", tn.name))
                            .with_help(format!("add `type {} = …` with the type for `{}`", tn.name, self.src_text(ty.span).trim())),
                    );
                    bad = true;
                    continue;
                }
            };
            types.push((tn.name.clone(), t));
        }
        let tsub = |n: &str, _s: Span| types.iter().find(|(t, _)| t == n).map(|(_, e)| e.clone());
        let renamer = |n: &str, s: Span| rename.get(n).map(|g| var(g, s));
        let none = |_: &str, _: Span| None;
        let nq = |_: &str, _: &str, _: Span| None;
        let rw = Rewrite { var: &renamer, con: &none, qualified: &nq };
        // In a signature, the class's function at this instance is this
        // instance's: the class's type doesn't tell which instance (#133).
        let mut own_fns: HashMap<String, String> = HashMap::new();
        for cm in cmembers.iter().filter(|_| !types.is_empty()) {
            let ClassMember::Fn { name, .. } = cm else { continue };
            let Some(g) = rename.get(&name.name) else { continue };
            own_fns.insert(name.name.clone(), g.clone());
            let class_mod = class_tid.map(|t| self.class_defs[&t].module.clone());
            if let Some(Sym::Def(d)) = class_mod.as_ref().and_then(|m| self.modules.get(m)).and_then(|mi| mi.values.get(&name.name)) {
                own_fns.insert(Self::sym_name(Sym::Def(*d)), g.clone());
            }
        }
        let own_fn = |n: &str, s: Span| own_fns.get(n).map(|g| var(g, s));
        let trw = Rewrite { var: &own_fn, con: &tsub, qualified: &nq };
        self.inst_heads.insert((self.cur.clone(), ty.span.start));
        let subst_ty = ty.clone();
        let param_c = param.clone();
        let sub = move |n: &str, _s: Span| if n == param_c { Some(subst_ty.clone()) } else { None };
        let srw = Rewrite { var: &sub, con: &none, qualified: &nq };
        let mut member_list = Vec::new();
        // Functions first: an instance missing one gets no lemmas, which
        // need its dictionary.
        let mut ordered: Vec<&ClassMember> = cmembers.iter().filter(|m| matches!(m, ClassMember::Fn { .. })).collect();
        ordered.extend(cmembers.iter().filter(|m| matches!(m, ClassMember::Lemma { .. })));
        for cm in ordered {
            if bad && matches!(cm, ClassMember::Lemma { .. }) {
                continue;
            }
            match cm {
                ClassMember::Type { .. } => continue,
                ClassMember::Fn { name, params, result, constraints, .. } => {
                    let given = members.iter().find_map(|m| match m {
                        InstMember::Fn { name: n, params, decreasing, body, span } if n.name == name.name => Some((params, decreasing, body, *span, n.span)),
                        _ => None,
                    });
                    let Some((iparams, decreasing, body, span, own_name)) = given else {
                        self.err(
                            Diagnostic::error("E0364", format!("`instance {text}` doesn't give `{}`", name.name), d.span)
                                .with_label(format!("`{}` missing", name.name))
                                .with_help(format!("add `fn {} {}` and its body", name.name, params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(" "))),
                        );
                        bad = true;
                        continue;
                    };
                    if iparams.len() != params.len() {
                        self.err(Diagnostic::error(
                            "E0365",
                            format!("`{}` takes {} in class `{}`, but {} here", name.name, count(params.len(), "parameter"), class.name, iparams.len()),
                            span,
                        ));
                        bad = true;
                        continue;
                    }
                    let map: HashMap<String, String> = params.iter().zip(iparams.iter()).map(|(a, b)| (a.name.clone(), b.name.clone())).collect();
                    let mut taken: Vec<String> = iparams.iter().map(|p| p.name.clone()).chain(result.iter().map(|r| r.name.clone())).collect();
                    taken.extend(head_vars.iter().cloned());
                    let constraints = &rename_vars(constraints, &hygiene(constraints, &param, &taken));
                    let mut cs = ctx_preds.clone();
                    let theirs = trw.constraints(&srw.constraints(&rename_binders(constraints, &map), &[]), &[]);
                    cs.extend(self.shown_here(foreign.as_deref(), constraints, theirs, span));
                    let mut bound: Vec<String> = iparams.iter().map(|p| p.name.clone()).collect();
                    bound.extend(result.iter().map(|r| r.name.clone()));
                    let gname = gen(&name.name);
                    member_list.push((name.name.clone(), decls.len()));
                    // The class's name for the result isn't written here.
                    let result = result.as_ref().map(|r| ident(&r.name, self.synthetic_span(span)));
                    decls.push(Decl {
                        export: Export::No,
                        kind: DeclKind::Fn {
                            partial: false,
                            name: ident(&gname, own_name),
                            params: iparams.clone(),
                            result,
                            constraints: cs,
                            decreasing: decreasing.as_ref().map(|e| rw.expr(e, &bound)),
                            body: rw.block(body, &bound),
                        },
                        span,
                    });
                    origins.push(Origin::InstMember(inst_ix));
                }
                ClassMember::Lemma { name, params, constraints, lets, ensures, .. } => {
                    let given = members.iter().find_map(|m| match m {
                        InstMember::Lemma { name: n, params, decreasing, proof, span } if n.name == name.name => {
                            Some((params.clone(), decreasing.clone(), proof.clone(), *span, n.span))
                        }
                        _ => None,
                    });
                    // Not given: proved by Z3, reported at the instance's header,
                    // with the class's names for the parameters.
                    let (iparams, decreasing, proof, span, name_span) = match given {
                        Some(g) => g,
                        None => {
                            let header = Span { start: d.span.start, end: ty.span.end };
                            let ps: Vec<Ident> = params.iter().map(|p| ident(&p.name, self.synthetic_span(header))).collect();
                            (ps, None, None, header, Span { start: d.span.start, end: d.span.start })
                        }
                    };
                    if iparams.len() != params.len() {
                        self.err(Diagnostic::error(
                            "E0365",
                            format!("`{}` takes {} in class `{}`, but {} here", name.name, count(params.len(), "parameter"), class.name, iparams.len()),
                            span,
                        ));
                        bad = true;
                        continue;
                    }
                    let mut taken: Vec<String> = iparams.iter().map(|p| p.name.clone()).collect();
                    taken.extend(head_vars.iter().cloned());
                    let hyg = hygiene(constraints, &param, &taken);
                    let constraints = &rename_vars(constraints, &hyg);
                    let mut map: HashMap<String, String> = params.iter().zip(iparams.iter()).map(|(a, b)| (a.name.clone(), b.name.clone())).collect();
                    map.extend(hyg);
                    let to_new = |n: &str, s: Span| map.get(n).map(|m| var(m, s));
                    let prw = Rewrite { var: &to_new, con: &none, qualified: &nq };
                    let mut cs = ctx_preds.clone();
                    let theirs = trw.constraints(&srw.constraints(&rename_binders(constraints, &map), &[]), &[]);
                    cs.extend(self.shown_here(foreign.as_deref(), constraints, theirs, span));
                    let mut bound: Vec<String> = iparams.iter().map(|p| p.name.clone()).collect();
                    let mut ls = Vec::new();
                    for (p, e) in lets {
                        ls.push((p.clone(), trw.expr(&srw.expr(&prw.expr(e, &[]), &[]), &[])));
                        pat_binds(p, &mut bound);
                    }
                    let mut ens = trw.expr(&srw.expr(&prw.expr(ensures, &[]), &[]), &[]);
                    if let Some(m) = foreign.as_deref() {
                        let at = self.synthetic_span(span);
                        let text = self.text_in(m, ensures.span);
                        self.text_override.insert((self.cur.clone(), at.start, at.end), text);
                        ens = respan(&ens, at);
                    }
                    let gname = gen(&name.name);
                    member_list.push((name.name.clone(), decls.len()));
                    decls.push(Decl {
                        export: Export::No,
                        kind: DeclKind::Lemma {
                            name: ident(&gname, name_span),
                            params: iparams.clone(),
                            constraints: cs,
                            decreasing: decreasing.as_ref().map(|e| rw.expr(e, &bound)),
                            lets: ls,
                            ensures: ens,
                            proof: proof.as_ref().map(|b| rw.block(b, &bound)),
                        },
                        span,
                    });
                    origins.push(Origin::InstMember(inst_ix));
                }
            }
        }
        if bad {
            // Keep what was generated (its errors are useful), but no dictionary.
            return;
        }
        // The dictionary.
        let sp = class.span;
        let mk = match class_tid {
            Some(t) => {
                let c = &self.class_defs[&t];
                format!("$mk#{}.{}", c.module, c.name)
            }
            None => format!("$mk#{}.{}", self.cur, class.name),
        };
        let mut body = con(&mk, sp);
        // Its types, each elaborated as a type (`()` is the unit type).
        for (_, t) in &types {
            let as_type = ast::RefineTy { param: None, own: false, dom: t.clone(), arrow: None, preds: Vec::new() };
            body = app(body, Expr { kind: ExprKind::Refine(Box::new(as_type)), span: t.span });
        }
        for cm in &cmembers {
            if let ClassMember::Fn { name, .. } = cm {
                body = app(body, var(&gen(&name.name), sp));
            }
        }
        let mut cs = ctx_preds.clone();
        cs.push(Constraint::Typed { name: ident("$dict", sp), mult: ast::Mult::Many, ty: app(con(&class.name, sp), ty.clone()) });
        decls.push(Decl {
            export: Export::No,
            kind: DeclKind::Fn {
                partial: false,
                name: ident(&text, Span { start: sp.start, end: sp.start }),
                params: Vec::new(),
                result: Some(ident("$dict", sp)),
                constraints: cs,
                decreasing: None,
                body: block(body),
            },
            span: d.span,
        });
        origins.push(Origin::InstDict(inst_ix));
        self.pending_insts.push(PendingInst {
            class: class_tid,
            class_name: class.name.clone(),
            head: head_ty.clone(),
            vars,
            context: ctx,
            span: d.span,
            text,
            members: member_list,
        });
    }

    /// After registration: the module's classes and instances into the tables.
    pub fn register_classes(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (name, param, members, span) in std::mem::take(&mut self.pending_classes) {
            let Some(Some(Sym::Ty(tid))) = m.decls.iter().zip(ids).find_map(|(d, id)| match &d.kind {
                DeclKind::Record { name: n, .. } if n.name == name => Some(*id),
                _ => None,
            }) else {
                continue;
            };
            let def = ClassDef { module: self.cur.clone(), name, param, members, tid, span };
            self.register_assoc(&def);
            self.class_defs.insert(tid, def);
        }
        for (k, (o, id)) in self.decl_origin.clone().iter().zip(ids).enumerate() {
            match (o, id) {
                (Origin::ClassMethod, Some(Sym::Def(d))) => {
                    self.class_methods.insert(*d);
                }
                (Origin::ClassLemma, Some(Sym::Def(d))) => {
                    self.class_lemmas.insert(*d);
                }
                (Origin::InstMember(_), Some(Sym::Def(d))) => {
                    let lemma = matches!(m.decls[k].kind, DeclKind::Lemma { .. });
                    self.def_class.insert(*d, if lemma { "lemma" } else { "function" });
                    if !lemma {
                        self.inst_fns.insert(*d);
                    }
                    // What an instance's functions do is visible wherever it is used.
                    self.transparent.insert(*d);
                }
                (Origin::InstDict(ix), Some(Sym::Def(d))) => {
                    self.transparent.insert(*d);
                    self.register_instance(*ix, *d, ids)
                }
                _ => {}
            }
        }
    }

    /// A class's types (#133): for each, `C.Name`, the definition
    /// `\t {d~C t} -> d.$Name` of type `t~K -> {C t} -> Type`, `K` the
    /// kind of the class's parameter.
    fn register_assoc(&mut self, c: &ClassDef) {
        let Some(&con) = self.g.tys[c.tid.0 as usize].ctors.first() else { return };
        let arity = c
            .members
            .iter()
            .flat_map(|m| match m {
                ClassMember::Fn { constraints, .. } | ClassMember::Lemma { constraints, .. } => constraints.as_slice(),
                ClassMember::Type { .. } => &[],
            })
            .filter_map(|k| match k {
                Constraint::Typed { ty, .. } => Some(applied_arity(ty, &c.param)),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        let mut kind = Tm::Univ(0);
        for _ in 0..arity {
            kind = Tm::Pi(Rc::from("_"), Mult::Many, Icit::Expl, Rc::new(Tm::Univ(0)), Rc::new(kind));
        }
        // Its types are the dictionary's first fields.
        for (k, t) in c.types().iter().enumerate() {
            let d = self.new_def(&format!("{}.{t}", c.name));
            let dict = Tm::TyConApp(c.tid, vec![Tm::Var(0)]);
            let info = &mut self.g.defs[d.0 as usize];
            info.ty = Tm::Pi(
                Rc::from(c.param.as_str()),
                Mult::Zero,
                Icit::Expl,
                Rc::new(kind.clone()),
                Rc::new(Tm::Pi(Rc::from("$d"), Mult::Many, Icit::Impl, Rc::new(dict), Rc::new(Tm::Univ(0)))),
            );
            info.body = Some(Tm::Lam(
                Rc::from(c.param.as_str()),
                Mult::Zero,
                Icit::Expl,
                Rc::new(Tm::Lam(Rc::from("$d"), Mult::Many, Icit::Impl, Rc::new(Tm::Field(Rc::new(Tm::Var(0)), con, k)))),
            ));
            self.transparent.insert(d);
            self.assoc_defs.insert((c.tid, t.clone()), d);
        }
    }

    fn register_instance(&mut self, ix: usize, def: DefId, ids: &[Option<Sym>]) {
        let p = self.pending_insts[ix].clone();
        self.dict_defs.insert(def);
        let class = match p.class {
            Some(t) => t,
            None => match self.resolve(&p.class_name, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => t,
                _ => return,
            },
        };
        // The head's type constructor.
        let mut h = &p.head;
        while let ExprKind::App(f, _) = &h.kind {
            h = f;
        }
        let key = match &h.kind {
            ExprKind::Tuple(xs) if xs.is_empty() => HeadKey::Unit,
            ExprKind::Tuple(_) => HeadKey::Pair,
            ExprKind::Con(n) => match self.resolve(n, true) {
                Some(Sym::Ty(t)) => HeadKey::Ty(t),
                Some(Sym::Def(_)) => {
                    self.err(
                        Diagnostic::error("E0281", format!("`instance {}` is for a type alias", p.text), p.head.span)
                            .with_help("write the instance for the type the alias stands for; it applies to the alias too"),
                    );
                    return;
                }
                _ => return,
            },
            _ => return,
        };
        // Rust's orphan rule (D136 b), by package: the class or the type is this package's.
        let pkg = self.package_of(&self.cur);
        let class_pkg = self.package_of(&self.class_defs[&class].module);
        let ty_pkg = match key {
            HeadKey::Ty(t) => self.package_of(&self.g.tys[t.0 as usize].module),
            HeadKey::Unit | HeadKey::Pair => "std".to_string(),
        };
        if pkg != class_pkg && pkg != ty_pkg {
            let cname = self.class_defs[&class].name.clone();
            self.err(
                Diagnostic::error("E0282", format!("`instance {}` must be in the package of `{cname}` or of the type", p.text), p.span)
                    .with_label("neither is declared in this package")
                    .with_help("an instance goes with its class or its type, so there is only ever one (Rust's orphan rule); wrap the type in a record of your own to give it this instance"),
            );
            return;
        }
        if let Some(other) = self.instances.get(&(class, key)) {
            let (om, os) = (other.module.clone(), other.span);
            let line = self.sources.get(&om).map(|f| f.line_col(os.start).0).unwrap_or(0);
            self.err(
                Diagnostic::error("E0283", format!("`instance {}` overlaps another instance", p.text), p.span)
                    .with_label(format!("`{}` is already declared at {om}:{line}", other.text))
                    .with_help("a type has one instance of each class; give the other order through a wrapper type, or `sort_as`/`sort_by`"),
            );
            return;
        }
        let context: Vec<(TyId, usize)> = p
            .context
            .iter()
            .filter_map(|(c, v)| match self.resolve(c, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => Some((t, p.vars.iter().position(|x| x == v)?)),
                _ => None,
            })
            .collect();
        let members: HashMap<String, DefId> = p
            .members
            .iter()
            .filter_map(|(n, k)| match ids.get(*k) {
                Some(Some(Sym::Def(d))) => Some((n.clone(), *d)),
                _ => None,
            })
            .collect();
        for d in members.values() {
            self.inst_member_of.insert(*d, def);
            // Using the dictionary may rely on the lemmas (termination, D136).
            if self.def_class.get(d) == Some(&"lemma") {
                self.calls.push(CallRec { caller: def, callee: *d, args: Vec::new(), same: Vec::new(), span: p.span, conds: Vec::new() });
            }
        }
        self.instances.insert(
            (class, key),
            InstInfo { class, def, module: self.cur.clone(), span: p.span, n_vars: p.vars.len(), context, members, text: p.text.clone() },
        );
    }

    /// A dictionary for `class` at `ty`, as a term at level `lvl`: one in
    /// scope, or an instance's, with its context found the same way.
    fn find_dict(&mut self, req: &InstReq, class: TyId, ty: &Val, depth: usize) -> Result<Tm, String> {
        if depth > 32 {
            return Err("instances nested too deeply".into());
        }
        let ty = self.force(ty);
        let tq = quote(&self.g, req.lvl, &ty);
        // A known type's dictionary is its instance's (coherence); one in
        // scope is used for a type parameter.
        let concrete = matches!(ty, Val::TyCon(..) | Val::TupleTy(_));
        for (l, c, t) in req.given.iter().filter(|_| !concrete) {
            if *c == class && format!("{:?}", quote(&self.g, req.lvl, &self.force(t))) == format!("{tq:?}") {
                return Ok(Tm::Var(req.lvl - l - 1));
            }
        }
        let (key, args) = match &ty {
            Val::TyCon(t, args) => (HeadKey::Ty(*t), args.clone()),
            // A type constructor not applied to its last argument (`List`
            // for `Functor`, M25): `\y -> T … y`.
            Val::Lam(_, _, _, c) => {
                let y = Val::var(req.lvl + 1000);
                match self.force(&apply_closure(&self.g, c, y)) {
                    Val::TyCon(t, mut args) if args.last().is_some_and(|a| matches!(a, Val::Neutral(Head::Var(v), sp) if *v == req.lvl + 1000 && sp.is_empty())) => {
                        args.pop();
                        (HeadKey::Ty(t), args)
                    }
                    _ => return Err("none".into()),
                }
            }
            // `()`, or a tuple: a pair of its first part and the rest.
            Val::TupleTy(xs) => {
                let xs = crate::core::flat_parts(&self.g, xs, true);
                match xs.len() {
                    0 => (HeadKey::Unit, Vec::new()),
                    1 => return Err("none".into()),
                    2 => (HeadKey::Pair, xs),
                    _ => (HeadKey::Pair, vec![xs[0].clone(), Val::TupleTy(xs[1..].to_vec())]),
                }
            }
            Val::Neutral(Head::Meta(_), _) => return Err("unknown".into()),
            _ => return Err("none".into()),
        };
        let Some(inst) = self.instances.get(&(class, key)).cloned() else { return Err("none".into()) };
        if args.len() < inst.n_vars {
            return Err("none".into());
        }
        let args = &args[args.len() - inst.n_vars..];
        let mut t = Tm::Def(inst.def);
        for a in args {
            t = Tm::App(Rc::new(t), Rc::new(quote(&self.g, req.lvl, a)), Icit::Impl, Mult::Zero);
        }
        for (c, v) in &inst.context {
            let d = self.find_dict(req, *c, &args[*v], depth + 1)?;
            t = Tm::App(Rc::new(t), Rc::new(d), Icit::Impl, Mult::Many);
        }
        // Using an instance of this module: a call, for termination (D136).
        if inst.module == self.cur && !req.in_spec {
            if let Some(caller) = req.owner {
                self.calls.push(CallRec { caller, callee: inst.def, args: Vec::new(), same: Vec::new(), span: req.span, conds: Vec::new() });
            }
        }
        Ok(t)
    }

    /// An instance's type defined through its own (#133): a dictionary
    /// that reads a type from the instance that is building it, through
    /// any chain of instances. Reported (E0225), and the type left unknown.
    fn assoc_cycle(&mut self, r: &InstReq, t: &Tm) -> bool {
        let (Some(name), Some(owner)) = (&r.assoc, r.owner) else { return false };
        let Tm::Def(target) = t.head() else { return false };
        if !self.dict_defs.contains(&owner) || !self.dict_defs.contains(target) {
            return false;
        }
        // Does `target` reach `owner`?
        let mut seen = vec![*target];
        let mut todo = vec![*target];
        let mut cycle = *target == owner;
        while let Some(d) = todo.pop() {
            for (a, b) in &self.assoc_edges {
                if *a == d && !seen.contains(b) {
                    cycle |= *b == owner;
                    seen.push(*b);
                    todo.push(*b);
                }
            }
        }
        if !cycle {
            self.assoc_edges.push((owner, *target));
            return false;
        }
        let shown = show(&self.g, &r.names, &quote(&self.g, r.lvl, &r.ty));
        let shown = if shown.contains(' ') { format!("({shown})") } else { shown };
        self.err(
            Diagnostic::error("E0225", format!("`{name} {shown}` depends on itself"), r.span)
                .with_help("an instance's type stands for the type it is given, so this would never end; give the type itself"),
        );
        true
    }

    /// Find the dictionaries asked for so far. With `last`, report those
    /// whose type still isn't known.
    pub fn solve_instances(&mut self, last: bool) {
        let reqs = std::mem::take(&mut self.inst_reqs);
        for r in reqs {
            if !matches!(self.force(&r.meta), Val::Neutral(Head::Meta(_), _)) {
                // Found already, by comparing types: a class's type may still
                // be defined through itself.
                if r.assoc.is_some() {
                    let t = quote(&self.g, r.lvl, &force_meta(&self.g, r.meta.clone()));
                    self.assoc_cycle(&r, &t);
                }
                continue;
            }
            match self.find_dict(&r, r.class, &r.ty, 0) {
                Ok(t) => {
                    if self.assoc_cycle(&r, &t) {
                        continue;
                    }
                    let env = Rc::new((0..r.lvl).map(Val::var).collect::<Vec<_>>());
                    let v = eval(&self.g, &env, &t);
                    let _ = unify(&self.g, r.lvl, &r.meta, &v);
                }
                Err(why) if why == "unknown" && !last => self.inst_reqs.push(r),
                Err(why) => {
                    // An unknown type in a reported mismatch: that error's (D141 c).
                    if why == "unknown" && self.unknowns(r.lvl, &r.ty).iter().any(|m| self.blamed.contains(m)) {
                        continue;
                    }
                    let cname = self.class_defs.get(&r.class).map(|c| c.name.clone()).unwrap_or_default();
                    let shown = match self.force(&r.ty) {
                        // `\y -> List y` is `List`.
                        Val::Lam(_, _, _, c) => match self.force(&apply_closure(&self.g, &c, Val::var(r.lvl))) {
                            Val::TyCon(t, args) if args.len() == 1 => self.g.tys[t.0 as usize].name.to_string(),
                            _ => show(&self.g, &r.names, &quote(&self.g, r.lvl, &r.ty)),
                        },
                        _ => show(&self.g, &r.names, &quote(&self.g, r.lvl, &r.ty)),
                    };
                    let shown_arg = if shown.contains(' ') { format!("({shown})") } else { shown.clone() };
                    let d = if why == "unknown" {
                        Diagnostic::error("E0285", format!("can't tell which instance of `{cname}` to use: the type isn't known here"), r.span)
                            .with_help("give the type, e.g. with a constraint `x~List Int` in the signature")
                    } else if matches!(self.force(&r.ty), Val::Neutral(Head::Var(_), _)) {
                        Diagnostic::error("E0284", format!("no instance of `{cname}` for `{shown}`"), r.span)
                            .with_label(format!("`{shown}` is a type parameter"))
                            .with_help(format!("add `{cname} {shown_arg}` to the function's signature"))
                    } else {
                        Diagnostic::error("E0284", format!("no instance of `{cname}` for `{shown}`"), r.span)
                            .with_label(format!("needs `{cname} {shown_arg}`"))
                            .with_help(format!("declare `instance {cname} …` for this type, beside the class or the type"))
                    };
                    self.err(d);
                }
            }
        }
    }

    /// A comparison just made waits for a dictionary (#133): remember it,
    /// to make again once the dictionary is found.
    pub fn note_postponed(&mut self, lvl: usize, expected: &Val, actual: &Val, span: Span, names: &[Name]) {
        let any = !self.g.postponed.borrow().is_empty();
        if any {
            self.g.postponed.borrow_mut().clear();
            self.waiting.push((lvl, expected.clone(), actual.clone(), span, names.to_vec()));
        }
    }

    /// `t` with each class's type at a known instance replaced by the
    /// instance's (#133): `NoOptions` for `Display.Options Int`, in messages.
    pub fn reduce_assoc(&self, lvl: usize, t: &Tm) -> Tm {
        if let (Tm::Def(d), args) = t.spine() {
            if args.len() == 2 && self.g.assoc_field(*d).is_some() {
                let env = Rc::new((0..lvl).map(Val::var).collect::<Vec<_>>());
                let v = force(&self.g, eval(&self.g, &env, t));
                let stuck = matches!(&v, Val::Neutral(_, sp) if matches!(sp.last(), Some(Elim::Field(..))));
                if !stuck {
                    return quote(&self.g, lvl, &v);
                }
                return t.clone();
            }
        }
        t.map_sub(|x, n| self.reduce_assoc(lvl + n, x))
    }

    /// Make again the comparisons that waited for a dictionary. One that
    /// still waits at the `last` try is dropped: its dictionary's type was
    /// never known, which its use reports (E0285).
    pub fn retry_waiting(&mut self, last: bool) {
        // A comparison made other than through `unify_at`: reported, if it
        // fails, at the last name checked.
        let strays: Vec<(usize, Val, Val)> = self.g.postponed.borrow_mut().drain(..).collect();
        for (l, a, b) in strays {
            let names = (0..l).map(|k| Name::from(format!("#{k}"))).collect();
            self.waiting.push((l, a, b, self.name_span, names));
        }
        for (l, a, b, span, names) in std::mem::take(&mut self.waiting) {
            let r = unify(&self.g, l, &a, &b);
            let again = {
                let mut p = self.g.postponed.borrow_mut();
                let again = !p.is_empty();
                p.clear();
                again
            };
            match r {
                Ok(()) if again => {
                    if !last {
                        self.waiting.push((l, a, b, span, names));
                    }
                }
                Ok(()) => {}
                Err(_) => {
                    let e = show(&self.g, &names, &self.reduce_assoc(l, &quote(&self.g, l, &a)));
                    let f = show(&self.g, &names, &self.reduce_assoc(l, &quote(&self.g, l, &b)));
                    self.err(Diagnostic::error("E0201", format!("type mismatch: expected `{e}`, found `{f}`"), span));
                }
            }
        }
    }

    /// A class's dictionary is built only by its instances (D136).
    pub fn check_dict_con(&mut self, c: ConId, span: Span) {
        let tid = self.g.cons[c.0 as usize].ty;
        if self.class_defs.contains_key(&tid) && !self.cur_fn.is_some_and(|d| self.dict_defs.contains(&d)) {
            let name = self.class_defs[&tid].name.clone();
            self.err(
                Diagnostic::error("E0287", format!("a dictionary of class `{name}` is built only by an instance"), span)
                    .with_help(format!("declare `instance {name} …`; its functions' bodies and lemmas' proofs are checked there")),
            );
        }
    }

    /// An implicit parameter being given a meta: if it is a dictionary,
    /// remember to find it.
    pub fn note_dict(&mut self, cx: &Cx, meta: &Val, dom: &Val, span: Span) {
        let Val::TyCon(tid, args) = self.force(dom) else { return };
        if !self.class_defs.contains_key(&tid) {
            return;
        }
        let Some(ty) = args.last().cloned() else { return };
        let mut given = Vec::new();
        for (l, loc) in cx.locals.iter().enumerate() {
            if let Val::TyCon(c, a) = self.force(&loc.ty) {
                if self.class_defs.contains_key(&c) {
                    if let Some(t) = a.last() {
                        given.push((l, c, t.clone()));
                    }
                }
            }
        }
        self.inst_reqs.push(InstReq {
            meta: meta.clone(),
            class: tid,
            ty,
            lvl: cx.lvl(),
            names: cx.names(),
            span,
            owner: self.cur_fn,
            in_spec: self.in_spec > 0,
            given,
            assoc: None,
        });
    }
}
