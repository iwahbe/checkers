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
use crate::syntax::token::Op;
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
    /// Its type parameters (several, #145).
    pub params: Vec<String>,
    pub members: Vec<ClassMember>,
    pub tid: TyId,
    pub span: Span,
    /// Its types' clauses (#176): the type's field, the clause's class, and
    /// the field holding its dictionary.
    pub clauses: Vec<(usize, TyId, usize)>,
}

/// A class's function gives a type for each parameter and its result
/// (else E0362), and no parameter of a function or lemma has the name of
/// one of the class's (else E0369); instances leave out a member that
/// doesn't.
fn member_ok(m: &ClassMember, cparams: &[String]) -> bool {
    if shadowed_param(m, cparams).is_some() {
        return false;
    }
    match m {
        ClassMember::Fn { params, result, constraints, .. } => {
            let typed = |n: &str| constraints.iter().any(|c| matches!(c, Constraint::Typed { name, .. } if name.name == n));
            params.iter().all(|p| typed(&p.name)) && result.as_ref().is_some_and(|r| typed(&r.name))
        }
        ClassMember::Lemma { .. } | ClassMember::Type { .. } => true,
    }
}

/// A parameter (or the result) of a class's function or lemma with the name
/// of one of the class's parameters (E0369): in the member's signature the
/// name would mean both.
fn shadowed_param<'m>(m: &'m ClassMember, cparams: &[String]) -> Option<&'m Ident> {
    let pinned = pinned_params(m, cparams);
    let names: Vec<&Ident> = match m {
        ClassMember::Fn { params, result, .. } => params.iter().filter(|p| !pinned.contains(&p.name)).chain(result).collect(),
        ClassMember::Lemma { params, .. } => params.iter().filter(|p| !pinned.contains(&p.name)).collect(),
        ClassMember::Type { .. } => return None,
    };
    names.into_iter().find(|p| cparams.contains(&p.name))
}

/// The class's parameters a function or lemma takes explicitly: a
/// parameter with the name of one, of type `ghost Type`, is that type
/// (#161). The dictionary doesn't hold it: its field, and an instance's
/// member, take it as a `ghost` parameter, the instance's type there.
fn pinned_params(m: &ClassMember, cparams: &[String]) -> Vec<String> {
    let (params, cs) = match m {
        ClassMember::Fn { params, constraints, .. } | ClassMember::Lemma { params, constraints, .. } => (params, constraints),
        ClassMember::Type { .. } => return Vec::new(),
    };
    params.iter().filter(|p| cparams.contains(&p.name) && super::decls::is_ghost_type(cs, &p.name)).map(|p| p.name.clone()).collect()
}

impl ClassDef {
    pub fn methods(&self) -> Vec<String> {
        self.members.iter().filter_map(|m| if let ClassMember::Fn { name, .. } = m { Some(name.name.clone()) } else { None }).collect()
    }

    /// Its types' names (#133).
    pub fn types(&self) -> Vec<String> {
        type_names(&self.members)
    }

    /// Where its functions start in the dictionary: after its types and
    /// their clauses' dictionaries (#133, #176).
    pub fn method_offset(&self) -> usize {
        self.types().len() + type_clauses(&self.members).len()
    }
}

/// The names of a class's types (#133).
fn type_names(members: &[ClassMember]) -> Vec<String> {
    members.iter().filter_map(|m| if let ClassMember::Type { name, .. } = m { Some(name.name.clone()) } else { None }).collect()
}

/// The class clauses on a class's types (`type Item : Ord Item`, #176),
/// in order: the type's name and the clause. A constraint is a clause when
/// it is a type constructor applied to arguments; anything else is a
/// predicate on the type's values.
fn type_clauses(members: &[ClassMember]) -> Vec<(String, &Expr)> {
    let mut out = Vec::new();
    for m in members {
        if let ClassMember::Type { name, constraints, .. } = m {
            for c in constraints {
                if let Constraint::Pred(e) = c {
                    if clause_on(e, &name.name) {
                        out.push((name.name.clone(), e));
                    }
                }
            }
        }
    }
    out
}

/// `C Name`: a clause on the class's type `Name` itself.
fn clause_on(e: &Expr, name: &str) -> bool {
    matches!(&e.kind, ExprKind::App(f, a) if matches!(f.kind, ExprKind::Con(_)) && matches!(&a.kind, ExprKind::Con(n) if n == name))
}

/// `C t …`: a type constructor applied to arguments.
fn is_clause_shape(e: &Expr) -> bool {
    let mut f = e;
    let mut n = 0;
    while let ExprKind::App(g, _) = &f.kind {
        f = g;
        n += 1;
    }
    n > 0 && matches!(f.kind, ExprKind::Con(_))
}

/// A class's type's predicates (#176): the name of its value (`u` of
/// `u~Unit`), if given, and the predicates.
fn type_preds(constraints: &[Constraint]) -> (Option<&Ident>, Vec<&Expr>) {
    let binder = constraints.iter().find_map(|c| if let Constraint::Typed { name, .. } = c { Some(name) } else { None });
    let preds = constraints
        .iter()
        .filter_map(|c| match c {
            Constraint::Pred(e) if !is_clause_shape(e) => Some(e),
            Constraint::Named(_, e) => Some(e),
            _ => None,
        })
        .collect();
    (binder, preds)
}

/// The base types of a class's type (#360): the types of its predicates'
/// value other than the type itself (`u~Int`, `u~Nat`), which combine as a
/// parameter's typings do.
fn type_bases<'a>(name: &str, constraints: &'a [Constraint]) -> Vec<&'a Expr> {
    constraints
        .iter()
        .filter_map(|c| match c {
            Constraint::Typed { ty, .. } if !matches!(&ty.kind, ExprKind::Con(n) if n == name) => Some(ty),
            _ => None,
        })
        .collect()
}

/// The names `e` mentions.
fn vars_in(e: &Expr) -> Vec<String> {
    let out = std::cell::RefCell::new(Vec::new());
    let see = |n: &str, _: Span| {
        out.borrow_mut().push(n.to_string());
        None
    };
    let none = |_: &str, _: Span| None;
    let nq = |_: &str, _: &str, _: Span| None;
    Rewrite { var: &see, con: &none, qualified: &nq }.expr(e, &[]);
    out.into_inner()
}

/// A class's type whose base types reach it again, through the class's
/// other types' base types (E0370): the type, and the path.
fn base_cycle(members: &[ClassMember], cparams: &[String]) -> Option<(String, Vec<String>, Span)> {
    let tnames = type_names(members);
    let edges: Vec<(String, Vec<String>, Span)> = members
        .iter()
        .filter_map(|m| match m {
            ClassMember::Type { name, constraints, .. } => {
                let bs = type_bases(&name.name, constraints);
                let span = bs.first().map(|b| b.span)?;
                let mut to: Vec<String> = Vec::new();
                for b in bs {
                    for n in vars_and_cons_in(b) {
                        if tnames.contains(&n) && !cparams.contains(&n) && !to.contains(&n) {
                            to.push(n);
                        }
                    }
                }
                Some((name.name.clone(), to, span))
            }
            _ => None,
        })
        .collect();
    for (start, _, span) in &edges {
        // Depth-first from `start`, back to it.
        let mut stack = vec![(start.clone(), vec![start.clone()])];
        let mut seen: Vec<String> = Vec::new();
        while let Some((n, path)) = stack.pop() {
            let Some((_, to, _)) = edges.iter().find(|(m, _, _)| *m == n) else { continue };
            for t in to {
                if t == start {
                    return Some((start.clone(), path.clone(), *span));
                }
                if !seen.contains(t) {
                    seen.push(t.clone());
                    let mut p = path.clone();
                    p.push(t.clone());
                    stack.push((t.clone(), p));
                }
            }
        }
    }
    None
}

/// The names (variables and constructors) `e` mentions.
fn vars_and_cons_in(e: &Expr) -> Vec<String> {
    let out = std::cell::RefCell::new(Vec::new());
    let see = |n: &str, _: Span| {
        out.borrow_mut().push(n.to_string());
        None
    };
    let nq = |_: &str, _: &str, _: Span| None;
    Rewrite { var: &see, con: &see, qualified: &nq }.expr(e, &[]);
    out.into_inner()
}


/// An instance's dictionary's field holding a dictionary for one of its
/// class's types (#176): found as an implicit argument is.
pub const FIND_DICT: &str = "$find_dict";

/// The dictionary's field holding the dictionary of a class's type's
/// `k`th clause (#176).
fn clause_field_name(name: &str, k: usize) -> String {
    format!("${name}#{k}")
}

/// Inside a class, its type `Name` is `C.Name a` (#133), `C.Name s h` for
/// a class of several parameters (#145).
fn assoc_use(class: &str, params: &[String], name: &str, s: Span) -> Expr {
    let mut e = Expr { kind: ExprKind::Field(Box::new(con(class, s)), ident(name, s)), span: s };
    for p in params {
        e = app(e, var(p, s));
    }
    e
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

/// An instance's function with a signature of its own (#225): the class's
/// signature at the instance, which it must refine.
pub struct InstRefine {
    pub class: String,
    pub member: String,
    /// The class's name for the result, and its constraints at the
    /// instance (the instance's context first).
    pub result: Option<Ident>,
    pub constraints: Vec<Constraint>,
    /// The class's declaration of the function, as written.
    pub declared: String,
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
    /// Its types, one for each of the class's parameters (#145).
    pub pats: Vec<InstPat>,
    /// Its context: a class and which of its variables (`Ord a`).
    pub context: Vec<(TyId, Vec<usize>)>,
    /// Its members by name (functions and lemmas).
    pub members: HashMap<String, DefId>,
    /// As written: `Ord (List a)`.
    pub text: String,
}

/// One of an instance's types: a type constructor applied to some of the
/// instance's variables (their positions), or one variable (#145).
#[derive(Clone, Debug)]
pub enum InstPat {
    Head(HeadKey, Vec<usize>),
    Var(usize),
}

/// What is known of a type an instance is asked for.
enum Shape {
    /// A type constructor and its arguments.
    Known(HeadKey, Vec<Val>),
    /// Not known yet.
    Unknown,
    /// A type parameter, a function type: no instance's type constructor.
    Other,
}

/// An instance being desugared in this module (registered with its
/// dictionary function).
#[derive(Clone)]
pub struct PendingInst {
    pub class: Option<TyId>,
    pub class_name: String,
    /// Its types, one for each of the class's parameters (#145).
    pub heads: Vec<Expr>,
    /// Each type's type constructor, or `None` for a variable.
    pub head_names: Vec<Option<String>>,
    pub vars: Vec<String>,
    /// Its context: classes of its variables (`Display a`).
    pub context: Vec<(String, Vec<String>)>,
    pub span: Span,
    pub text: String,
    pub members: Vec<(String, usize)>,
}

/// A dictionary to find once the types are known: the meta standing for it.
#[derive(Clone)]
pub struct InstReq {
    pub meta: Val,
    pub class: TyId,
    /// The types it is for, one for each of the class's parameters.
    pub tys: Vec<Val>,
    pub lvl: usize,
    pub names: Vec<Name>,
    pub span: Span,
    pub owner: Option<DefId>,
    pub in_spec: bool,
    /// Dictionaries in scope: level, class, types.
    pub given: Vec<(usize, TyId, Vec<Val>)>,
    /// For a class's type, `C.Name` (#133): the dictionary is read for it.
    pub assoc: Option<String>,
    /// In an instance's signature: that instance, used if the type is
    /// never known (#146).
    pub fallback: Option<SigInst>,
    /// Where it is asked for, for a check of the instance found through a
    /// refinement alias (#226).
    pub cx: Option<Rc<Cx>>,
    /// For a type's header's clause (#385): the type.
    pub of_type: Option<TyId>,
    /// Asked in the signature of an instance's function or dictionary.
    pub instance_sig: Option<DefId>,
}

/// A dictionary found through a refinement alias (#226): the instance of
/// the type the alias stands for, checked at the end of the module to
/// give the alias's values wherever it returns the class's type.
#[derive(Clone)]
pub struct AliasDict {
    /// The unknown it was found for, if asked for by a use (not by an
    /// instance's context).
    pub meta: Option<MetaId>,
    pub cx: Rc<Cx>,
    pub span: Span,
    pub owner: Option<DefId>,
    pub class: TyId,
    /// The types it is for, aliases kept, and which one is the alias.
    pub tys: Vec<Val>,
    pub pos: usize,
    /// The dictionary, at the context's level.
    pub dict: Tm,
    /// The instance's functions, by name, and the instance as written.
    pub members: HashMap<String, DefId>,
    pub inst_text: String,
}

/// The instance whose member's signature is being elaborated (#146): its
/// class, and for each of its types (#145) the type constructor (`None`
/// for a bare variable) and the variables.
#[derive(Clone)]
pub struct SigInst {
    pub class: TyId,
    pub heads: Vec<(Option<HeadKey>, Vec<String>)>,
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
        ExprKind::Template(t, ps) => ExprKind::Template(go(t), map_pieces(ps, |x| respan(x, s), Some(s))),
        k => k.clone(),
    };
    Expr { kind, span: s }
}

/// A template's pieces with `f` applied to each expression in them, and
/// with every span `s` if given.
fn map_pieces(ps: &[ast::TemplatePiece], mut f: impl FnMut(&Expr) -> Expr, s: Option<Span>) -> Vec<ast::TemplatePiece> {
    ps.iter()
        .map(|p| match p {
            ast::TemplatePiece::Text(t, sp) => ast::TemplatePiece::Text(t.clone(), s.unwrap_or(*sp)),
            ast::TemplatePiece::Hole { value, options, span } => ast::TemplatePiece::Hole {
                value: value.as_ref().map(&mut f),
                options: options.iter().map(&mut f).collect(),
                span: s.unwrap_or(*span),
            },
        })
        .collect()
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

/// "`a` and `b`", "`a`, `b` and `c`" (or "or").
fn joined(xs: &[String], conj: &str) -> String {
    match xs.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("`{}` {conj} `{last}`", rest.join("`, `")),
        Some((last, _)) => format!("`{last}`"),
        None => String::new(),
    }
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
fn method_vars(tys: &[&Expr], params: &[String], out: &mut Vec<String>) {
    fn go(e: &Expr, param: &[String], out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Var(v) if !param.contains(v) && !out.contains(v) => out.push(v.clone()),
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
        go(t, params, out);
    }
}

/// The class function's own type variables that would be captured by the
/// instance's names (its parameters, or its type's variables), each given a
/// fresh name: `b` in `g~(a -> b)` when the instance names a parameter `b`.
fn hygiene(cs: &[Constraint], params: &[String], taken: &[String]) -> HashMap<String, String> {
    let tys: Vec<&Expr> = cs
        .iter()
        .filter_map(|c| match c {
            Constraint::Typed { ty, .. } => Some(ty),
            _ => None,
        })
        .collect();
    let mut own = Vec::new();
    method_vars(&tys, params, &mut own);
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

/// An instance's member's parameters, each one that is the class's
/// (#161) with the instance's type for it: one written `_` is named, by the
/// class's name for it unless another parameter has that name, so that its
/// type can be given.
fn pinned_named(iparams: &[Ident], params: &[Ident], skip: &[usize], subst_ty: &dyn Fn(&str) -> Expr) -> (Vec<Ident>, Vec<(Ident, Expr)>) {
    let mut all = iparams.to_vec();
    let mut pinned = Vec::new();
    for &k in skip {
        if all[k].name == "_" {
            let base = params[k].name.clone();
            let mut name = base.clone();
            let mut n = 1;
            while all.iter().any(|p| p.name == name) {
                name = format!("{base}{n}");
                n += 1;
            }
            all[k].name = name;
        }
        pinned.push((all[k].clone(), subst_ty(&params[k].name)));
    }
    (all, pinned)
}

impl Elab {
    /// An instance's member's parameters that are the class's (#161):
    /// each `name~ghost Type` and `name == T`, `T` the instance's type for
    /// it. A use passes the instance's type there, as its own body does.
    fn pinned_constraints(&mut self, pinned: &[(Ident, Expr)]) -> Vec<Constraint> {
        let mut out = Vec::new();
        for (p, ty) in pinned {
            let n = &p.name;
            let s = self.synthetic_span(p.span);
            out.push(Constraint::Typed { name: ident(n, s), mult: ast::Mult::Ghost, ty: con("Type", s) });
            let text = format!("{n} == {}", self.src_text(ty.span));
            self.text_override.insert((self.cur.clone(), s.start, s.end), text);
            let eq = Expr { kind: ExprKind::Binary(Op::EqEq, Box::new(var(n, s)), Box::new(respan(ty, s))), span: s };
            out.push(Constraint::Pred(eq));
        }
        out
    }
}

/// `blk` with `let name = ty` first, for each of a class's parameters an
/// instance's member names (#161): there, it is the instance's type.
fn with_types(blk: &Block, types: &[(String, Expr)]) -> Block {
    let mut stmts: Vec<Stmt> = types
        .iter()
        .filter(|(n, _)| n != "_")
        // Elaborated as a type: `Ascii` is the type, not its record's constructor.
        // `ghost`, as the class's parameter is.
        .map(|(n, ty)| {
            let as_type = ast::RefineTy { param: None, own: false, dom: ty.clone(), arrow: None, preds: Vec::new() };
            Stmt::GhostLet(ident(n, ty.span), Expr { kind: ExprKind::Refine(Box::new(as_type)), span: ty.span })
        })
        .collect();
    if stmts.is_empty() {
        return blk.clone();
    }
    stmts.extend(blk.stmts.iter().cloned());
    Block { stmts, result: blk.result.clone(), span: blk.span }
}

/// Drop the parameters at `skip` from a member's, and the class's
/// constraints giving them types (#161).
fn without<T: Clone>(xs: &[T], skip: &[usize]) -> Vec<T> {
    xs.iter().enumerate().filter(|(k, _)| !skip.contains(k)).map(|(_, x)| x.clone()).collect()
}

fn untyped(cs: &[Constraint], names: &[String]) -> Vec<Constraint> {
    cs.iter().filter(|c| !matches!(c, Constraint::Typed { name, .. } if names.contains(&name.name))).cloned().collect()
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
/// A default's text (`text`, from `start`) at an instance: each of the
/// class's parameters replaced by the instance's type (`heads`),
/// parenthesized where it is applied or an argument (`List (Box b)`).
fn default_text(text: &str, start: u32, e: &Expr, heads: &HashMap<String, String>) -> String {
    fn walk(e: &Expr, arg: bool, heads: &HashMap<String, String>, out: &mut Vec<(Span, String)>) {
        match &e.kind {
            ExprKind::Var(n) => {
                if let Some(h) = heads.get(n) {
                    let simple = !h.contains(char::is_whitespace) || h.starts_with('(') && h.ends_with(')');
                    out.push((e.span, if arg && !simple { format!("({h})") } else { h.clone() }));
                }
            }
            ExprKind::App(f, x) => {
                walk(f, true, heads, out);
                walk(x, true, heads, out);
            }
            ExprKind::Arrow(a, b) => {
                walk(a, true, heads, out);
                walk(b, false, heads, out);
            }
            ExprKind::Tuple(xs) | ExprKind::List(xs) | ExprKind::Par(xs) => xs.iter().for_each(|x| walk(x, false, heads, out)),
            _ => {}
        }
    }
    let mut subs = Vec::new();
    walk(e, false, heads, &mut subs);
    subs.sort_by_key(|(s, _)| s.start);
    let mut out = String::new();
    let mut at = 0;
    for (s, h) in subs {
        let (a, b) = ((s.start - start) as usize, (s.end - start) as usize);
        if a < at || b > text.len() {
            continue;
        }
        out.push_str(&text[at..a]);
        out.push_str(&h);
        at = b;
    }
    out.push_str(&text[at..]);
    out
}

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
            ExprKind::When(w) => {
                let binds = w.binds.iter().map(|(n, e)| (n.clone(), self.expr(e, bound))).collect();
                let mut b = bound.to_vec();
                b.extend(w.binds.iter().map(|(n, _)| n.name.clone()));
                ExprKind::When(ast::When { binds, sched: w.sched.clone(), body: self.block(&w.body, &b), span: w.span })
            }
            ExprKind::Block(blk) => ExprKind::Block(self.block(blk, bound)),
            ExprKind::Template(t, ps) => ExprKind::Template(go(t), map_pieces(ps, |x| self.expr(x, bound), None)),
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
                Stmt::GhostLet(x, e) => {
                    let e = self.expr(e, &b);
                    b.push(x.name.clone());
                    Stmt::GhostLet(x.clone(), e)
                }
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

/// Whether `name` occurs free in `e`, respecting what lambdas, `match`,
/// `let` and `forall` bind.
pub(super) fn mentions_var(e: &Expr, name: &str) -> bool {
    let found = std::cell::Cell::new(false);
    let f = |n: &str, _: Span| {
        if n == name {
            found.set(true);
        }
        None
    };
    let none = |_: &str, _: Span| None;
    let nq = |_: &str, _: &str, _: Span| None;
    Rewrite { var: &f, con: &none, qualified: &nq }.expr(e, &[]);
    found.get()
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

/// A class member's constraints at an instance: its parameters renamed by
/// `map` to the instance's names, and the class's parameters and types
/// replaced by `subst` (the instance's types). The renaming goes through
/// names no program can write, so an instance's parameter named as the
/// class's parameter (`fn size s` in `Seq s`) isn't taken for it.
fn at_instance(cs: &[Constraint], map: &HashMap<String, String>, subst: &dyn Fn(&[Constraint]) -> Vec<Constraint>) -> Vec<Constraint> {
    let (fresh, back) = fresh_names(map);
    rename_binders(&subst(&rename_binders(cs, &fresh)), &back)
}

/// `map` through fresh names: to them, and from them to `map`'s values.
fn fresh_names(map: &HashMap<String, String>) -> (HashMap<String, String>, HashMap<String, String>) {
    let mut fresh = HashMap::new();
    let mut back = HashMap::new();
    for (k, (from, to)) in map.iter().enumerate() {
        let f = format!("$inst{k}");
        fresh.insert(from.clone(), f.clone());
        back.insert(f, to.clone());
    }
    (fresh, back)
}

impl Elab {
    /// Is `e` a class clause (`Ord a`)? The class, if so.
    pub fn class_clause(&self, e: &Expr) -> Option<TyId> {
        let ExprKind::App(f, _) = &e.kind else { return None };
        let mut f: &Expr = f;
        // `Hole s h`: a class of several parameters (#145).
        while let ExprKind::App(g, _) = &f.kind {
            f = g;
        }
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

    pub(super) fn sym_name(s: Sym) -> String {
        match s {
            Sym::Def(d) => format!("$sym#D{}", d.0),
            Sym::Ty(t) => format!("$sym#T{}", t.0),
            Sym::Con(c) => format!("$sym#C{}", c.0),
            Sym::Univ => "$sym#U0".into(),
            Sym::Len => "len".into(),
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
                ClassMember::Type { name, default, constraints, span } => {
                    let bound: Vec<String> = constraints
                        .iter()
                        .filter_map(|c| if let Constraint::Typed { name, .. } = c { Some(name.name.clone()) } else { None })
                        .collect();
                    ClassMember::Type {
                        name: name.clone(),
                        default: default.as_ref().map(|e| rw.expr(e, &[])),
                        constraints: rw.constraints(constraints, &bound),
                        span: *span,
                    }
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
        self.sources.get(m).map(|f| crate::elab::source_text(&f.text, span, false)).unwrap_or_default()
    }

    /// The text of a predicate in another module, a block keeping its lines.
    fn expr_text_in(&self, m: &str, e: &Expr) -> String {
        self.sources.get(m).map(|f| crate::elab::source_text(&f.text, e.span, crate::elab::has_block(e))).unwrap_or_default()
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
                let text = match o {
                    Constraint::Typed { ty, .. } => self.text_in(m, ty.span),
                    Constraint::Pred(e) | Constraint::Named(_, e) => self.expr_text_in(m, e),
                };
                self.text_override.insert((self.cur.clone(), s.start, s.end), text);
                respan_constraints(std::slice::from_ref(c), s).remove(0)
            })
            .collect()
    }

    /// Desugar the module's classes and instances (D136). Returns the new
    /// module and where each of its declarations came from.
    pub fn desugar_classes(&mut self, m: &ast::Module) -> (ast::Module, Vec<Origin>) {
        // What another module's instances left is about its declarations.
        self.member_heads.clear();
        self.inst_refines.clear();
        self.transparent_members.clear();
        let has = m.decls.iter().any(|d| matches!(d.kind, DeclKind::Class { .. } | DeclKind::Instance { .. }));
        if !has {
            return (m.clone(), vec![Origin::Written; m.decls.len()]);
        }
        let mut decls = Vec::new();
        let mut origins = Vec::new();
        let local: HashMap<String, (Vec<String>, Vec<ClassMember>, Span)> = m
            .decls
            .iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Class { name, params, members } => {
                    Some((name.name.clone(), (params.iter().map(|p| p.name.clone()).collect(), members.clone(), name.span)))
                }
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
                DeclKind::Class { name, params, members } => self.desugar_class(d, name, params, members, &local, &mut decls, &mut origins),
                DeclKind::Instance { class, tys, context, members } => {
                    self.desugar_instance(d, class, tys, context, members, &local, &mut decls, &mut origins)
                }
                _ => {
                    decls.push(d.clone());
                    origins.push(Origin::Written);
                }
            }
        }
        (ast::Module { name: m.name.clone(), imports: m.imports.clone(), decls, templates: m.templates }, origins)
    }

    #[allow(clippy::too_many_arguments)]
    fn desugar_class(
        &mut self,
        d: &Decl,
        name: &Ident,
        params: &[Ident],
        members: &[ClassMember],
        local: &HashMap<String, (Vec<String>, Vec<ClassMember>, Span)>,
        decls: &mut Vec<Decl>,
        origins: &mut Vec<Origin>,
    ) {
        let sp = name.span;
        let pnames: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
        let mut clause = con(&name.name, sp);
        for p in params {
            clause = app(clause, var(&p.name, sp));
        }
        // Each parameter once.
        for (k, p) in params.iter().enumerate() {
            if params[..k].iter().any(|q| q.name == p.name) {
                self.err(Diagnostic::error("E0350", format!("`{}` is defined twice in class `{}`", p.name, name.name), p.span));
            }
        }
        let mut fields = Vec::new();
        let mut type_fields = Vec::new();
        let mut clause_fields = Vec::new();
        let mut seen = HashSet::new();
        // Its types (#133): in the dictionary, a field of its own; in its
        // functions' and lemmas' signatures, `C.Name a`.
        let tnames = type_names(members);
        let to_field = |n: &str, s: Span| if tnames.iter().any(|t| t == n) { Some(var(&assoc_field_name(n), s)) } else { None };
        let cname = name.name.clone();
        let to_assoc = |n: &str, s: Span| if tnames.iter().any(|t| t == n) { Some(assoc_use(&cname, &pnames, n, s)) } else { None };
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
            if let Some(p) = shadowed_param(mem, &pnames) {
                self.err(
                    Diagnostic::error("E0369", format!("parameter `{}` of `{}` has the name of the class's parameter `{}`", p.name, mname.name, p.name), p.span)
                        .with_label(format!("the class's parameter is `{}`", p.name))
                        .with_help("give the parameter another name"),
                );
                continue;
            }
            match mem {
                ClassMember::Type { name: t, constraints: tcs, .. } => {
                    self.class_type_constraints(t, tcs, local, &frw, &mut clause_fields);
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
                    // A class's parameter it takes explicitly (#161) is a
                    // `ghost` parameter of the field too (`None` here): the
                    // instance's function takes it, as the class's does.
                    let pinned = pinned_params(mem, &pnames);
                    let mut missing = Vec::new();
                    let mut tys: Vec<Option<Expr>> = Vec::new();
                    for p in params {
                        if pinned.contains(&p.name) {
                            tys.push(None);
                            continue;
                        }
                        match typed(&p.name) {
                            Some(t) => tys.push(Some(t)),
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
                    let refs: Vec<&Expr> = tys.iter().flatten().chain(std::iter::once(&rty)).collect();
                    method_vars(&refs, &pnames, &mut own);
                    let ren: HashMap<String, String> = own.iter().map(|v| (v.clone(), format!("'{v}"))).collect();
                    let to_q = |n: &str, s: Span| ren.get(n).map(|m| var(m, s));
                    let none = |_: &str, _: Span| None;
                    let nq = |_: &str, _: &str, _: Span| None;
                    let qrw = Rewrite { var: &to_q, con: &none, qualified: &nq };
                    let mut fty = qrw.expr(&frw.expr(&rty, &[]), &[]);
                    for (t, p) in tys.into_iter().zip(params).rev() {
                        fty = match t {
                            Some(t) => {
                                let span = t.span;
                                Expr { kind: ExprKind::Arrow(Box::new(qrw.expr(&frw.expr(&t, &[]), &[])), Box::new(fty)), span }
                            }
                            // Named apart from the class's parameter, which
                            // the rest of the type means by its name.
                            None => {
                                let span = p.span;
                                Expr {
                                    kind: ExprKind::Refine(Box::new(ast::RefineTy {
                                        param: Some(ident(&format!("${}", p.name), span)),
                                        own: false,
                                        dom: con("Type", span),
                                        arrow: Some((None, fty)),
                                        preds: Vec::new(),
                                    })),
                                    span,
                                }
                            }
                        };
                    }
                    // Its own class clauses (`Seq s`): implicit parameters
                    // of the field, the dictionaries each call passes, so
                    // an instance's function gets them as any function
                    // with a clause does.
                    let clauses: Vec<&Expr> = constraints
                        .iter()
                        .filter_map(|c| match c {
                            Constraint::Pred(e) if self.is_class_clause(e, local) => Some(e),
                            _ => None,
                        })
                        .collect();
                    for (k, c) in clauses.iter().enumerate().rev() {
                        let span = c.span;
                        fty = Expr {
                            kind: ExprKind::Refine(Box::new(ast::RefineTy {
                                param: Some(ident(&format!("'$c{k}"), span)),
                                own: false,
                                dom: qrw.expr(&frw.expr(c, &[]), &[]),
                                arrow: Some((None, fty)),
                                preds: Vec::new(),
                            })),
                            span,
                        };
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
                    // `std.string`'s `Debug` (#126): every type has an
                    // instance, so `debug` needs no clause; it is the
                    // runtime's printer, which finds a hand-written
                    // instance through the value's constructor.
                    let derived = self.is_debug_class(&name.name);
                    let mut cs = if derived { Vec::new() } else { vec![Constraint::Pred(clause.clone())] };
                    cs.extend(arw.constraints(constraints, &[]));
                    if derived {
                        call = var("__builtin", at_end);
                    }
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
        // With several parameters (#145), each function and lemma mentions
        // each of them in its parameters' types: otherwise a use couldn't
        // tell which instance it means.
        if params.len() > 1 {
            for mem in members {
                let (mname, mparams, cs, what) = match mem {
                    ClassMember::Fn { name, params, constraints, .. } => (name, params, constraints, "function"),
                    ClassMember::Lemma { name, params, constraints, .. } => (name, params, constraints, "lemma"),
                    ClassMember::Type { .. } => continue,
                };
                if shadowed_param(mem, &pnames).is_some() {
                    continue;
                }
                let tys: Vec<&Expr> = cs
                    .iter()
                    .filter_map(|c| match c {
                        Constraint::Typed { name, ty, .. } if mparams.iter().any(|p| p.name == name.name) => Some(ty),
                        _ => None,
                    })
                    .collect();
                let pinned = pinned_params(mem, &pnames);
                // A parameter a type equation fixes from the others counts
                // as mentioned (#209): `Seq.Elem s == t` finds `t` from `s`.
                let mut known: Vec<String> = tys.iter().flat_map(|t| vars_in(t)).chain(pinned.iter().cloned()).collect();
                let teqs: Vec<(&Expr, &Expr)> = cs.iter().filter_map(|c| match c {
                    Constraint::Pred(e) => self.teq_sides(cs, e),
                    _ => None,
                }).collect();
                for _ in 0..teqs.len() {
                    for (a, b) in &teqs {
                        for (x, y) in [(a, b), (b, a)] {
                            if vars_in(y).iter().all(|v| known.contains(v)) {
                                known.extend(vars_in(x));
                            }
                        }
                    }
                }
                for p in params {
                    if !pinned.contains(&p.name) && !known.contains(&p.name) && !tys.iter().any(|t| super::decls::mentions_free(t, &p.name)) {
                        let ps: Vec<&str> = params.iter().map(|q| q.name.as_str()).collect();
                        self.err(
                            Diagnostic::error("E0368", format!("{what} `{}` doesn't mention the class's parameter `{}`", mname.name, p.name), mname.span)
                                .with_label(format!("no parameter's type mentions `{}`", p.name))
                                .with_help(format!(
                                    "a use of `{}` must tell which instance of `{} {}` it means: give one of its parameters a type that mentions `{}`, or take `{}` itself as a parameter `{}~ghost Type`",
                                    mname.name,
                                    name.name,
                                    ps.join(" "),
                                    p.name,
                                    p.name,
                                    p.name
                                )),
                        );
                        break;
                    }
                }
            }
        }
        // Each parameter's kind: `Type`, or `Type -> Type` if the members
        // apply it to one argument, and so on (M25).
        let mut rcs = Vec::new();
        for param in params {
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
            if arity > 0 {
                rcs.push(Constraint::Typed { name: param.clone(), mult: ast::Mult::Many, ty: kind });
            }
        }
        decls.push(Decl {
            export: if d.export == Export::No { Export::No } else { Export::Abstract },
            kind: DeclKind::Record {
                name: name.clone(),
                params: params.iter().map(|p| ast::Param { polarity: None, name: p.clone() }).collect(),
                constraints: rcs,
                fields: type_fields.into_iter().chain(clause_fields).chain(fields).collect(),
            },
            span: d.span,
        });
        origins.push(Origin::ClassRecord);
        self.pending_classes.push((name.name.clone(), pnames, members.to_vec(), name.span));
    }

    /// A class's type's constraints (#176): each class clause (`Ord Item`)
    /// is a field of the dictionary, after the types; its predicates name a
    /// value of it (`u~Unit`), and are checked at each instance.
    fn class_type_constraints(
        &mut self,
        t: &Ident,
        cs: &[Constraint],
        local: &HashMap<String, (Vec<String>, Vec<ClassMember>, Span)>,
        frw: &Rewrite,
        clause_fields: &mut Vec<ast::Field>,
    ) {
        let mut first: Option<&Ident> = None;
        for c in cs {
            match c {
                Constraint::Typed { name, .. } => {
                    if first.is_some_and(|f| f.name != name.name) {
                        self.err(
                            Diagnostic::error("E0370", format!("the predicates on `{}` name one value of it", t.name), name.span)
                                .with_label("a second name")
                                .with_help(format!("each predicate is about any one value of `{}`: use the first name", t.name)),
                        );
                        continue;
                    }
                    // `u~Unit` names a value; any other type is a base type
                    // (#360), and several combine (checked once elaborated).
                    first = Some(name);
                }
                Constraint::Pred(e) if is_clause_shape(e) => {
                    let ExprKind::App(f, _) = &e.kind else { continue };
                    if !clause_on(e, &t.name) {
                        let shown = match &f.kind {
                            ExprKind::Con(n) => n.clone(),
                            _ => "C".into(),
                        };
                        self.err(
                            Diagnostic::error("E0370", format!("a clause on `{}` is a class of `{}` itself", t.name, t.name), e.span)
                                .with_label(format!("this is not a class of `{}` alone", t.name))
                                .with_help(format!("write e.g. `{shown} {}`; a clause about the class's parameter goes on its functions", t.name)),
                        );
                        continue;
                    }
                    let k = clause_fields.len();
                    let ty = if self.is_class_clause(e, local) {
                        frw.expr(e, &[])
                    } else {
                        let ExprKind::Con(n) = &f.kind else { continue };
                        self.err(
                            Diagnostic::error("E0280", format!("`{n}` is not a class"), f.span)
                                .with_help(format!("a clause on `{}` names a class declared with `class`", t.name)),
                        );
                        Expr { kind: ExprKind::Unit, span: e.span }
                    };
                    clause_fields.push(ast::Field { name: ident(&clause_field_name(&t.name, k), e.span), mult: ast::Mult::Many, ty, preds: Vec::new(), span: e.span });
                }
                _ => {}
            }
        }
        let (binder, preds) = type_preds(cs);
        let Some(first) = preds.first() else { return };
        if binder.is_none() {
            self.err(
                Diagnostic::error("E0370", format!("a predicate on `{}` needs a name for its value", t.name), first.span)
                    .with_help(format!("name it first: `type {} : x~{}, …`", t.name, t.name)),
            );
        }
    }

    /// Is `e` a class clause (`Seq s`), of a class declared elsewhere or in
    /// this module (`local`, not registered yet)?
    fn is_class_clause(&self, e: &Expr, local: &HashMap<String, (Vec<String>, Vec<ClassMember>, Span)>) -> bool {
        let mut f = e;
        let mut args = 0;
        while let ExprKind::App(g, _) = &f.kind {
            f = g;
            args += 1;
        }
        match &f.kind {
            ExprKind::Con(n) if args > 0 => local.contains_key(n) || self.class_clause(e).is_some(),
            _ => false,
        }
    }

    /// The header of the instance of this module that `def` is a member of
    /// or builds the dictionary of, as written (`instance Ord (List a) :
    /// Ord a`).
    fn instance_header(&self, def: DefId) -> Option<String> {
        let inst = self.instances.values().flatten().find(|i| i.module == self.cur && (i.def == def || i.members.values().any(|m| *m == def)))?;
        let text = self.sources.get(&self.cur)?.text.get(inst.span.start as usize..inst.span.end as usize)?;
        let line = text.lines().next()?.trim_end();
        let line = line.split(" #").next()?.trim_end();
        line.starts_with("instance ").then(|| line.to_string())
    }

    /// Whether the class `name` declared here is `std.string`'s `Debug`
    /// (#126).
    pub fn is_debug_class(&self, name: &str) -> bool {
        self.cur == "std.string" && name == "Debug"
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

    /// One of an instance's types, checked: a type constructor applied to
    /// distinct type variables (pushed onto `vars`), or, except for the
    /// first type of a class of several parameters, a bare type variable
    /// (#145). The type (`()` for the prelude's `Unit`) and its type
    /// constructor's name (`None` for a variable), or `None` if reported.
    #[allow(clippy::too_many_arguments)]
    fn instance_arg(
        &mut self,
        text: &str,
        class: &Ident,
        ty: &Expr,
        param: (usize, &str, usize),
        want: usize,
        vars: &mut Vec<String>,
        local: &HashMap<String, (Vec<String>, Vec<ClassMember>, Span)>,
    ) -> Option<(Expr, Option<String>)> {
        let (index, pname, nparams) = param;
        // A bare variable (#145): any type at this parameter.
        if let ExprKind::Var(v) = &ty.kind {
            if nparams > 1 && index == 0 {
                self.err(
                    Diagnostic::error("E0281", format!("the first type of `instance {text}` can't be a type variable"), ty.span)
                        .with_label("a type variable")
                        .with_help(format!(
                            "an instance is found by its first type: write it for a type constructor, e.g. `instance {} (List a) …`",
                            class.name
                        )),
                );
                return None;
            }
            if nparams > 1 {
                if vars.contains(v) {
                    self.err(
                        Diagnostic::error("E0281", format!("`instance {text}` uses the type variable `{v}` twice"), ty.span)
                            .with_label(format!("`{v}` again"))
                            .with_help("an instance's types have distinct type variables; give this one its own name"),
                    );
                    return None;
                }
                vars.push(v.clone());
                return Some((ty.clone(), None));
            }
        }
        // `()`, written so or as the prelude's `Unit`: the tuple type of no
        // elements, a type constructor with no parameters.
        let unit_head = Expr { kind: ExprKind::Tuple(Vec::new()), span: ty.span };
        let head_ty = if self.is_unit_head(ty) { unit_head } else { ty.clone() };
        // The head: a type constructor applied to distinct type variables.
        let mut args = Vec::new();
        let mut h = &head_ty;
        while let ExprKind::App(f, a) = &h.kind {
            args.push((**a).clone());
            h = f;
        }
        args.reverse();
        let ok = match &h.kind {
            ExprKind::Con(_) => args.iter().all(|a| matches!(&a.kind, ExprKind::Var(v) if !vars.contains(v) && { vars.push(v.clone()); true })),
            ExprKind::Tuple(xs) if args.is_empty() && matches!(xs.len(), 0 | 2) => xs.iter().all(|a| matches!(&a.kind, ExprKind::Var(v) if !vars.contains(v) && { vars.push(v.clone()); true })),
            _ => false,
        };
        let shown_ty = self.src_text(ty.span).trim().to_string();
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
                return None;
            }
            _ => {}
        }
        if !ok {
            self.err(
                Diagnostic::error("E0281", format!("`instance {text}` must be for a type applied to distinct type variables"), ty.span)
                    .with_label("not a type constructor applied to variables")
                    .with_help("write it for every element type, e.g. `instance Ord (List a) : Ord a`"),
            );
            return None;
        }
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
                        .with_help("write the instance for the type the alias stands for: the class at the alias uses it, where its signature shows that the values it gives are of the alias"),
                );
                return None;
            }
            ExprKind::Con(n) => match self.local_ty_params.get(n) {
                Some(k) => Some(*k),
                None => match self.resolve(n, true) {
                    Some(Sym::Ty(t)) => Some(self.g.tys[t.0 as usize].params.len()),
                    // An unknown type: nothing of the instance can be checked.
                    None if !self.local_names.contains_key(n) => {
                        let mut e = Diagnostic::error("E0204", format!("unknown name `{n}`"), h.span).with_label("not found");
                        if let Some(m) = self.private_in_imports(n) {
                            e = self.private_help(e, &self.cur, &m, n);
                        }
                        self.err(e);
                        return None;
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
                        return None;
                    }
                },
            },
            _ => Some(args.len()),
        };
        // Its kind: a class over types of `n` parameters (M25) takes a type
        // constructor short of `n` arguments.
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
                if nparams > 1 {
                    format!("give it its parameters, as in `({shown_ty} {})`", vs.join(" "))
                } else {
                    format!("give it its parameters, as in `instance {} ({shown_ty} {})`", class.name, vs.join(" "))
                }
            } else if want < given {
                "leave the last parameters off; the class's functions supply them".to_string()
            } else {
                format!("`{}` is for a type that takes its element type as its last parameter, like `List` or `Option`", class.name)
            };
            let whose = if nparams > 1 { format!("`{}`'s parameter `{pname}`", class.name) } else { format!("`{}`", class.name) };
            self.err(Diagnostic::error("E0286", format!("{whose} is for {}, but `{shown_ty}` is {}", shown(want), plain(given)), ty.span).with_help(fix));
            return None;
        }
        let name = match &h.kind {
            ExprKind::Tuple(xs) => format!("tuple{}", xs.len()),
            ExprKind::Con(n) => n.clone(),
            _ => String::new(),
        };
        Some((head_ty, Some(name)))
    }

    #[allow(clippy::too_many_arguments)]
    fn desugar_instance(
        &mut self,
        d: &Decl,
        class: &Ident,
        tys: &[Expr],
        context: &[Expr],
        members: &[InstMember],
        local: &HashMap<String, (Vec<String>, Vec<ClassMember>, Span)>,
        decls: &mut Vec<Decl>,
        origins: &mut Vec<Origin>,
    ) {
        let (first, last) = (tys[0].span, tys[tys.len() - 1].span);
        let tys_span = Span { start: first.start, end: last.end };
        let tys_text = self.src_text(tys_span).trim().to_string();
        let text = format!("{} {tys_text}", class.name);
        // The class: declared here, or imported.
        let (cparams, cmembers, class_tid) = match local.get(&class.name) {
            Some((p, ms, _)) => (p.clone(), ms.clone(), None),
            None => match self.resolve(&class.name, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => {
                    let c = self.class_defs[&t].clone();
                    (c.params.clone(), self.members_for_instance(&c), Some(t))
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
        // A type for each of the class's parameters (#145).
        if tys.len() != cparams.len() {
            let want = count(cparams.len(), "type");
            let help = if cparams.len() == 1 {
                format!("put the type in parentheses: `instance {} ({tys_text})`", class.name)
            } else {
                format!("give a type for each of {}", joined(&cparams, "and"))
            };
            self.err(
                Diagnostic::error("E0292", format!("`{}` takes {want}, but `instance {text}` gives {}", class.name, tys.len()), tys_span)
                    .with_label(format!("{} here", count(tys.len(), "type")))
                    .with_help(help),
            );
            return;
        }
        // Each type's kind: a class over types of `n` parameters (M25)
        // takes a type constructor short of `n` arguments.
        let want_of = |param: &str| {
            cmembers
                .iter()
                .flat_map(|m| match m {
                    ClassMember::Fn { constraints, .. } | ClassMember::Lemma { constraints, .. } => constraints.as_slice(),
                    ClassMember::Type { .. } => &[],
                })
                .filter_map(|c| match c {
                    Constraint::Typed { ty, .. } => Some(applied_arity(ty, param)),
                    _ => None,
                })
                .max()
                .unwrap_or(0)
        };
        let mut vars: Vec<String> = Vec::new();
        let mut heads: Vec<Expr> = Vec::new();
        let mut head_names: Vec<Option<String>> = Vec::new();
        for (k, ty) in tys.iter().enumerate() {
            let want = want_of(&cparams[k]);
            let Some((h, n)) = self.instance_arg(&text, class, ty, (k, &cparams[k], cparams.len()), want, &mut vars, local) else { return };
            heads.push(h);
            head_names.push(n);
        }
        // Its context: classes of its variables.
        let mut ctx = Vec::new();
        for c in context {
            let mut cargs = Vec::new();
            let mut f = c;
            while let ExprKind::App(g, a) = &f.kind {
                cargs.push(a);
                f = g;
            }
            cargs.reverse();
            let good = match &f.kind {
                ExprKind::Con(cn) if !cargs.is_empty() => {
                    let vs: Option<Vec<String>> = cargs
                        .iter()
                        .map(|a| match &a.kind {
                            ExprKind::Var(v) if vars.contains(v) => Some(v.clone()),
                            _ => None,
                        })
                        .collect();
                    match vs {
                        Some(vs) => {
                            ctx.push((cn.clone(), vs));
                            true
                        }
                        None => false,
                    }
                }
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
        let cmembers: Vec<ClassMember> = cmembers.into_iter().filter(|m| member_ok(m, &cparams)).collect();
        // Two instances here for the same class whose types can be the same
        // (one elsewhere is found when it is registered): at each position,
        // the same type constructor, or a variable in either (#145).
        let overlaps = |p: &PendingInst| {
            p.class_name == class.name
                && p.head_names.len() == head_names.len()
                && p.head_names.iter().zip(&head_names).all(|(a, b)| a.is_none() || b.is_none() || a == b)
        };
        if let Some(prev) = self.pending_insts.iter().find(|p| overlaps(p)) {
            let line = self.sources.get(&self.cur).map(|f| f.line_col(prev.span.start).0).unwrap_or(0);
            let prev_text = prev.text.clone();
            let help = if cparams.len() == 1 {
                "a type has one instance of each class; give the other order through a wrapper type, or `sort_as`/`sort_by`"
            } else {
                "no two instances of a class may match the same types; make one of them for other types"
            };
            self.err(
                Diagnostic::error("E0283", format!("`instance {text}` overlaps another instance"), d.span)
                    .with_label(format!("`{prev_text}` is already declared on line {line}"))
                    .with_help(help),
            );
            return;
        }
        let inst_ix = self.pending_insts.len();
        let mut head_vars = Vec::new();
        method_vars(&tys.iter().collect::<Vec<_>>(), &[], &mut head_vars);
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
        let header = Span { start: d.span.start, end: tys_span.end };
        let mut types: Vec<(String, Expr)> = Vec::new();
        // Those given here, with where: their predicates are checked (#176).
        let mut given_types: Vec<(String, Expr, Span)> = Vec::new();
        for cm in &all_members {
            let ClassMember::Type { name: tn, default, .. } = cm else { continue };
            let given = members.iter().find_map(|m| match m {
                InstMember::Type { name, ty, span } if name.name == tn.name => Some((ty.clone(), *span)),
                _ => None,
            });
            if let Some((t, span)) = &given {
                given_types.push((tn.name.clone(), t.clone(), *span));
            }
            let given = given.map(|(t, _)| t);
            let t = match (given, default) {
                (Some(t), _) => t,
                (None, Some(dflt)) => {
                    let module = foreign.clone().unwrap_or_else(|| self.cur.clone());
                    let mut t = match foreign.as_deref() {
                        Some(m) => {
                            let at = self.synthetic_span(header);
                            let text = self.text_in(m, dflt.span);
                            self.text_override.insert((self.cur.clone(), at.start, at.end), text);
                            respan(dflt, at)
                        }
                        None => dflt.clone(),
                    };
                    // The class's parameters are this instance's types,
                    // and the default is shown with them (`List Int`).
                    if cparams.iter().any(|p| super::decls::mentions_free(dflt, p)) {
                        let heads: HashMap<String, String> = cparams.iter().cloned().zip(tys.iter().map(|t| self.src_text(t.span))).collect();
                        let text = default_text(&self.text_in(&module, dflt.span), dflt.span.start, dflt, &heads);
                        let sub = |n: &str, _s: Span| cparams.iter().position(|p| p == n).map(|k| tys[k].clone());
                        t = Rewrite { var: &sub, con: &|_, _| None, qualified: &|_, _, _| None }.expr(&t, &[]);
                        let at = self.synthetic_span(if foreign.is_some() { header } else { dflt.span });
                        self.text_override.insert((self.cur.clone(), at.start, at.end), text);
                        t.span = at;
                    }
                    t
                }
                (None, None) => {
                    self.err(
                        Diagnostic::error("E0364", format!("`instance {text}` doesn't give `{}`", tn.name), d.span)
                            .with_label(format!("`{}` missing", tn.name))
                            .with_help(format!("add `type {} = …` with the type for `{tys_text}`", tn.name)),
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
        let trw = Rewrite { var: &none, con: &tsub, qualified: &nq };
        for ty in tys {
            self.inst_heads.insert((self.cur.clone(), ty.span.start));
        }
        let subst: HashMap<String, Expr> = cparams.iter().cloned().zip(tys.iter().cloned()).collect();
        let subst_ty = |n: &str| subst[n].clone();
        let sub = |n: &str, _s: Span| subst.get(n).cloned();
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
                        InstMember::Fn { transparent, name: n, params, sig, decreasing, body, span } if n.name == name.name => {
                            Some((params, sig, decreasing, body, *span, n.span, *transparent))
                        }
                        _ => None,
                    });
                    let Some((iparams, isig, decreasing, body, span, own_name, transparent)) = given else {
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
                    // The class's parameters it takes explicitly (#161): the
                    // instance's function takes them too, each the instance's
                    // type, which its body has by that name. Its own
                    // signature is over the rest.
                    let pinned = pinned_params(cm, &cparams);
                    let skip: Vec<usize> = (0..params.len()).filter(|k| pinned.contains(&params[*k].name)).collect();
                    let pinned_types: Vec<(String, Expr)> = skip.iter().map(|k| (iparams[*k].name.clone(), subst_ty(&params[*k].name))).collect();
                    let (all_iparams, named) = pinned_named(iparams, params, &skip, &subst_ty);
                    let all_iparams = &all_iparams;
                    let pinned_cs = self.pinned_constraints(&named);
                    let (params, iparams) = (&without(params, &skip), &without(iparams, &skip));
                    let constraints = &untyped(constraints, &pinned);
                    let mut map: HashMap<String, String> = params.iter().zip(iparams.iter()).map(|(a, b)| (a.name.clone(), b.name.clone())).collect();
                    let mut taken: Vec<String> = all_iparams.iter().map(|p| p.name.clone()).chain(result.iter().map(|r| r.name.clone())).collect();
                    taken.extend(head_vars.iter().cloned());
                    // The class's name for the result, if the instance names
                    // a parameter so (`fn debug s` for `-> s`), is another.
                    let result = match result {
                        Some(r) if all_iparams.iter().any(|p| p.name == r.name) => {
                            let mut k = 1;
                            let fresh = loop {
                                let n = format!("{}{k}", r.name);
                                if !taken.contains(&n) && !params.iter().any(|p| p.name == n) {
                                    break n;
                                }
                                k += 1;
                            };
                            map.insert(r.name.clone(), fresh.clone());
                            taken.push(fresh.clone());
                            Some(ident(&fresh, r.span))
                        }
                        r => r.clone(),
                    };
                    let constraints = &rename_vars(constraints, &hygiene(constraints, &cparams, &taken));
                    let mut cs = ctx_preds.clone();
                    let theirs = at_instance(constraints, &map, &|c| trw.constraints(&srw.constraints(c, &[]), &[]));
                    cs.extend(self.shown_here(foreign.as_deref(), constraints, theirs, span));
                    cs.extend(pinned_cs.iter().cloned());
                    let mut bound: Vec<String> = all_iparams.iter().map(|p| p.name.clone()).collect();
                    bound.extend(result.iter().map(|r| r.name.clone()));
                    let gname = gen(&name.name);
                    member_list.push((name.name.clone(), decls.len()));
                    // The class's name for the result isn't written here.
                    let result = result.as_ref().map(|r| ident(&r.name, self.synthetic_span(span)));
                    // A signature of its own (#225): the function has it, and
                    // the class's, at this instance, is kept to check that it
                    // refines it. A parameter that is the class's (#161) is
                    // the instance's type in it, as in the body.
                    let (result, cs) = match isig {
                        None => (result, cs),
                        Some((iresult, icons)) => {
                            let pinned_names: Vec<String> = pinned_types.iter().map(|(n, _)| n.clone()).collect();
                            for c in icons {
                                if let Constraint::Typed { name: pn, mult, ty } = c {
                                    let is_type = matches!(&ty.kind, ExprKind::Con(t) if t == "Type") && *mult == ast::Mult::Ghost;
                                    if pinned_names.contains(&pn.name) && !is_type {
                                        self.err(
                                            Diagnostic::error("E0365", format!("`{}` takes the class's parameter: its type is `ghost Type`", pn.name), ty.span)
                                                .with_help(format!("write `{}~ghost Type`", pn.name)),
                                        );
                                        bad = true;
                                    }
                                }
                            }
                            let to_type = |n: &str, _s: Span| pinned_types.iter().find(|(p, _)| p == n).map(|(_, t)| t.clone());
                            let prw = Rewrite { var: &to_type, con: &none, qualified: &nq };
                            // The context is the instance's; a clause of it
                            // written here too is the same one.
                            let ctx_texts: Vec<String> = context.iter().map(|c| self.src_text(c.span)).collect();
                            let own: Vec<Constraint> = untyped(icons, &pinned_names)
                                .into_iter()
                                .filter(|c| !matches!(c, Constraint::Pred(e) if ctx_texts.contains(&self.src_text(e.span))))
                                .collect();
                            let mut ics = ctx_preds.clone();
                            // The class's types are the instance's (#133).
                            ics.extend(trw.constraints(&prw.constraints(&own, &[]), &[]));
                            ics.extend(pinned_cs.iter().cloned());
                            let text = match foreign.as_deref() {
                                Some(m) => self.text_in(m, cm.span()),
                                None => self.src_text(cm.span()),
                            };
                            let declared = text.split_whitespace().collect::<Vec<_>>().join(" ");
                            self.inst_refines.insert(
                                decls.len(),
                                InstRefine { class: class.name.clone(), member: name.name.clone(), result, constraints: cs, declared },
                            );
                            (iresult.clone(), ics)
                        }
                    };
                    decls.push(Decl {
                        export: Export::No,
                        kind: DeclKind::Fn {
                            partial: false,
                            name: ident(&gname, own_name),
                            params: all_iparams.clone(),
                            result,
                            constraints: cs,
                            decreasing: decreasing.as_ref().map(|e| rw.expr(e, &bound)),
                            body: with_types(&rw.block(body, &bound), &pinned_types),
                        },
                        span,
                    });
                    origins.push(Origin::InstMember(inst_ix));
                    self.member_heads.insert(decls.len() - 1, (class.name.clone(), heads.clone()));
                    if transparent {
                        self.transparent_members.insert(decls.len() - 1);
                    }
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
                            let header = Span { start: d.span.start, end: tys_span.end };
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
                    // The class's parameters it takes explicitly (#161), as
                    // for a function: taken, each the instance's type.
                    let pinned = pinned_params(cm, &cparams);
                    let skip: Vec<usize> = (0..params.len()).filter(|k| pinned.contains(&params[*k].name)).collect();
                    let pinned_types: Vec<(String, Expr)> = skip.iter().map(|k| (iparams[*k].name.clone(), subst_ty(&params[*k].name))).collect();
                    let (all_iparams, named) = pinned_named(&iparams, params, &skip, &subst_ty);
                    let pinned_cs = self.pinned_constraints(&named);
                    let (params, iparams) = (&without(params, &skip), without(&iparams, &skip));
                    let constraints = &untyped(constraints, &pinned);
                    let mut taken: Vec<String> = all_iparams.iter().map(|p| p.name.clone()).collect();
                    taken.extend(head_vars.iter().cloned());
                    let hyg = hygiene(constraints, &cparams, &taken);
                    let constraints = &rename_vars(constraints, &hyg);
                    let mut map: HashMap<String, String> = params.iter().zip(iparams.iter()).map(|(a, b)| (a.name.clone(), b.name.clone())).collect();
                    map.extend(hyg);
                    // Through fresh names, as `at_instance` does.
                    let (fresh, back) = fresh_names(&map);
                    let to_fresh = |n: &str, s: Span| fresh.get(n).map(|m| var(m, s));
                    let from_fresh = |n: &str, s: Span| back.get(n).map(|m| var(m, s));
                    let prw = Rewrite { var: &to_fresh, con: &none, qualified: &nq };
                    let brw = Rewrite { var: &from_fresh, con: &none, qualified: &nq };
                    let mut cs = ctx_preds.clone();
                    let theirs = at_instance(constraints, &map, &|c| trw.constraints(&srw.constraints(c, &[]), &[]));
                    cs.extend(self.shown_here(foreign.as_deref(), constraints, theirs, span));
                    cs.extend(pinned_cs);
                    let mut bound: Vec<String> = all_iparams.iter().map(|p| p.name.clone()).collect();
                    let mut ls = Vec::new();
                    for (p, e) in lets {
                        ls.push((p.clone(), brw.expr(&trw.expr(&srw.expr(&prw.expr(e, &[]), &[]), &[]), &[])));
                        pat_binds(p, &mut bound);
                    }
                    let mut ens = brw.expr(&trw.expr(&srw.expr(&prw.expr(ensures, &[]), &[]), &[]), &[]);
                    if let Some(m) = foreign.as_deref() {
                        let at = self.synthetic_span(span);
                        let text = self.expr_text_in(m, ensures);
                        self.text_override.insert((self.cur.clone(), at.start, at.end), text);
                        ens = respan(&ens, at);
                    }
                    let gname = gen(&name.name);
                    member_list.push((name.name.clone(), decls.len()));
                    decls.push(Decl {
                        export: Export::No,
                        kind: DeclKind::Lemma {
                            name: ident(&gname, name_span),
                            params: all_iparams,
                            constraints: cs,
                            decreasing: decreasing.as_ref().map(|e| rw.expr(e, &bound)),
                            lets: ls,
                            ensures: ens,
                            proof: proof.as_ref().map(|b| with_types(&rw.block(b, &bound), &pinned_types)),
                        },
                        span,
                    });
                    origins.push(Origin::InstMember(inst_ix));
                    self.member_heads.insert(decls.len() - 1, (class.name.clone(), heads.clone()));
                }
            }
        }
        // Each predicate on a class's type holds of every value of the type
        // this instance gives it, or takes as the default (#176): a lemma,
        // proved by Z3, reported at the instance's `type Name = T` (or its
        // header). A predicate is about the class's functions, which are the
        // instance's, so a default is checked at each instance too.
        for cm in &all_members {
            let ClassMember::Type { name: tn, constraints: tcs, .. } = cm else { continue };
            let Some((_, ty)) = types.iter().find(|(n, _)| *n == tn.name) else { continue };
            let at = &given_types.iter().find(|(n, _, _)| *n == tn.name).map(|(_, _, s)| *s).unwrap_or(header);
            let (Some(binder), preds) = type_preds(tcs) else { continue };
            let module = foreign.clone().unwrap_or_else(|| self.cur.clone());
            // Its base type (#360): the instance's type must be it, up to
            // refinement, with its refinement; a lemma of no statement of
            // its own, checked first. Where it fails, the predicates aren't.
            // At this instance: its types for the class's parameters, its
            // types for the class's types.
            let bases: Vec<Expr> = type_bases(&tn.name, tcs).into_iter().map(|b| respan(&trw.expr(&srw.expr(b, &[]), &[]), *at)).collect();
            let mut checks: Vec<(String, Expr)> = Vec::new();
            if !bases.is_empty() {
                checks.push((format!("{text}.{}#base", tn.name), con("True", *at)));
            }
            for (k, p) in preds.iter().enumerate() {
                checks.push((format!("{text}.{}#{k}", tn.name), (*p).clone()));
            }
            for (lname, p) in checks {
                let p = &p;
                self.class_type_checks.insert(lname.clone(), (format!("{}.{}", class.name, tn.name), self.src_text(ty.span)));
                if !bases.is_empty() {
                    self.class_type_bases_at.insert(lname.clone(), (bases.clone(), binder.name.clone(), lname.ends_with("#base")));
                }
                // The class's predicate, shown at the instance's type.
                let s = self.synthetic_span(*at);
                let ptext = if lname.ends_with("#base") { self.src_text(ty.span) } else { self.expr_text_in(&module, p) };
                self.text_override.insert((self.cur.clone(), s.start, s.end), ptext);
                let ens = respan(&trw.expr(&srw.expr(p, std::slice::from_ref(&binder.name)), std::slice::from_ref(&binder.name)), s);
                let mut cs = ctx_preds.clone();
                cs.push(Constraint::Typed { name: ident(&binder.name, s), mult: ast::Mult::Many, ty: ty.clone() });
                decls.push(Decl {
                    export: Export::No,
                    kind: DeclKind::Lemma {
                        name: ident(&lname, Span { start: at.start, end: at.start }),
                        params: vec![ident(&binder.name, s)],
                        constraints: cs,
                        decreasing: None,
                        lets: Vec::new(),
                        ensures: ens,
                        proof: None,
                    },
                    span: *at,
                });
                origins.push(Origin::InstMember(inst_ix));
                self.member_heads.insert(decls.len() - 1, (class.name.clone(), heads.clone()));
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
        // Its types' clauses (#176): each dictionary found for the type
        // given, reported at `type Name = T` (or the header, for a default).
        for (tn, _) in type_clauses(&all_members) {
            let at = given_types.iter().find(|(n, _, _)| *n == tn).map(|(_, _, s)| *s).unwrap_or(header);
            body = app(body, var(FIND_DICT, at));
        }
        for cm in &cmembers {
            if let ClassMember::Fn { name, .. } = cm {
                body = app(body, var(&gen(&name.name), sp));
            }
        }
        let mut cs = ctx_preds.clone();
        let dict_ty = tys.iter().fold(con(&class.name, sp), |f, t| app(f, t.clone()));
        cs.push(Constraint::Typed { name: ident("$dict", sp), mult: ast::Mult::Many, ty: dict_ty });
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
            heads,
            head_names,
            vars,
            context: ctx,
            span: d.span,
            text,
            members: member_list,
        });
    }

    /// After registration: the module's classes and instances into the tables.
    pub fn register_classes(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (name, params, members, span) in std::mem::take(&mut self.pending_classes) {
            let Some(Some(Sym::Ty(tid))) = m.decls.iter().zip(ids).find_map(|(d, id)| match &d.kind {
                DeclKind::Record { name: n, .. } if n.name == name => Some(*id),
                _ => None,
            }) else {
                continue;
            };
            // Its types' clauses' dictionaries: fields after its types (#176).
            let tnames = type_names(&members);
            let clauses = type_clauses(&members)
                .iter()
                .enumerate()
                .filter_map(|(j, (t, e))| {
                    let ty = tnames.iter().position(|n| n == t)?;
                    Some((ty, self.class_clause(e)?, tnames.len() + j))
                })
                .collect();
            let def = ClassDef { module: self.cur.clone(), name, params, members, tid, span, clauses };
            self.register_assoc(&def);
            self.class_defs.insert(tid, def);
        }
        for (k, (o, id)) in self.decl_origin.clone().iter().zip(ids).enumerate() {
            match (o, id) {
                (Origin::ClassMethod, Some(Sym::Def(d))) => {
                    self.class_methods.insert(*d);
                    self.g.well_known.class_fns.insert(*d);
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
                    // An instance's function is sealed outside its module, as
                    // any function is, unless marked `transparent` (#249).
                    if lemma || self.transparent_members.contains(&k) {
                        self.transparent.insert(*d);
                    }
                }
                (Origin::InstDict(ix), Some(Sym::Def(d))) => {
                    self.transparent.insert(*d);
                    self.register_instance(*ix, *d, ids)
                }
                _ => {}
            }
        }
    }

    /// The predicates on this module's classes' types (#176), elaborated
    /// once their functions' signatures are (a predicate may use them):
    /// over the class's parameters, its dictionary, and a value of the type.
    pub fn elab_class_type_preds(&mut self) {
        let mut defs: Vec<ClassDef> = self.class_defs.values().filter(|c| c.module == self.cur).cloned().collect();
        defs.sort_by_key(|c| c.span.start);
        for c in defs {
            let Some(&con) = self.g.tys[c.tid.0 as usize].ctors.first() else { continue };
            let tnames = c.types();
            let (cname, pnames) = (c.name.clone(), c.params.clone());
            let to_assoc = |n: &str, s: Span| if tnames.iter().any(|t| t == n) { Some(assoc_use(&cname, &pnames, n, s)) } else { None };
            let none = |_: &str, _: Span| None;
            let nq = |_: &str, _: &str, _: Span| None;
            let arw = Rewrite { var: &none, con: &to_assoc, qualified: &nq };
            for (k, m) in c.members.iter().filter(|m| matches!(m, ClassMember::Type { .. })).enumerate() {
                let ClassMember::Type { name: member, constraints, .. } = m else { continue };
                let (Some(binder), preds) = type_preds(constraints) else { continue };
                if preds.is_empty() {
                    continue;
                }
                self.g.fuel.set(DEFAULT_FUEL);
                let mut cx = Cx::default();
                let params = self.g.tys[c.tid.0 as usize].params.clone();
                let mut pvals = Vec::new();
                for (n, kind) in &params {
                    let kv = self.eval(&cx, kind);
                    let l = cx.bind(n, kv, Mult::Zero);
                    pvals.push(Val::var(l));
                }
                let d = cx.bind("$d", Val::TyCon(c.tid, pvals.into()), Mult::Many);
                // `C.Name a`, as written (its field of the dictionary in scope).
                let tname = &tnames[k];
                let ty = match self.assoc_defs.get(&(c.tid, tname.clone())) {
                    Some(acc) => {
                        let mut v = Val::Neutral(Head::Def(*acc), Rc::new(Vec::new()));
                        for l in 0..params.len() {
                            v = crate::core::app(&self.g, v, Val::var(l), Icit::Expl);
                        }
                        crate::core::app(&self.g, v, Val::var(d), Icit::Impl)
                    }
                    None => crate::core::elim(&self.g, Val::var(d), Elim::Field(con, k)),
                };
                cx.bind(&binder.name, ty, Mult::Many);
                let mut out = Vec::new();
                for p in preds {
                    // Without a base type, an operator on its values is
                    // E0210: both ways to say it (#360).
                    let text = self.src_text(p.span);
                    let via_fn = super::rename_words(&text, &[(binder.name.clone(), format!("code {} {}", c.params.join(" "), binder.name))]);
                    self.in_class_type_pred = Some(format!(
                        "`{t}` has no operations of its own: give it a base type, as in `type {t} : {u}~Int, {text}`, or reach its values through one of the class's functions, as in `{via_fn}`",
                        t = member.name,
                        u = binder.name,
                    ));
                    let e = arw.expr(p, std::slice::from_ref(&binder.name));
                    out.push(self.elab_pred(&mut cx, &e, false));
                    self.solve_deferred();
                }
                self.in_class_type_pred = None;
                for p in &mut out {
                    p.tm = crate::core::zonk_metas(&self.g, cx.lvl(), &p.tm);
                }
                // Whether they can all hold (E0457).
                let mut all = cx.clone();
                for p in &out {
                    let v = self.eval(&all, &p.tm);
                    all.assume(v);
                }
                let conds = out.iter().map(|p| Some(p.text.clone())).collect();
                let kind = VacuityKind::ClassType { subject: binder.name.clone() };
                self.ask_vacuity(&all, kind, &format!("{cname}.{}", member.name), member.span, conds, None);
                self.class_type_preds.insert((con, k), out);
            }
        }
    }

    /// Its types' base types (#360), elaborated over the class's parameters
    /// and a dictionary (its other types are read from it). Typings of the
    /// one value combine, as a parameter's do: they must agree (E0372). A
    /// base type that reaches its own type is E0370.
    /// This module's classes' types' base types, once the classes'
    /// parameters are bound.
    pub fn register_module_type_bases(&mut self) {
        let mut defs: Vec<ClassDef> = self.class_defs.values().filter(|c| c.module == self.cur).cloned().collect();
        defs.sort_by_key(|c| c.span.start);
        for c in defs {
            self.register_type_bases(&c);
        }
    }

    fn register_type_bases(&mut self, c: &ClassDef) {
        let Some(&con) = self.g.tys[c.tid.0 as usize].ctors.first() else { return };
        if let Some((t, path, span)) = base_cycle(&c.members, &c.params) {
            let through = if path.len() > 1 { format!(", through `{}`", path[1..].join("`, `")) } else { String::new() };
            self.err(
                Diagnostic::error("E0370", format!("the base type of `{t}` mentions `{t}` itself{through}"), span)
                    .with_label("no type can be a refinement of a type built from itself")
                    .with_help(format!("give `{t}` a base type that doesn't mention it")),
            );
            return;
        }
        let tnames = c.types();
        let params = self.g.tys[c.tid.0 as usize].params.clone();
        let none = |_: &str, _: Span| None;
        let nq = |_: &str, _: &str, _: Span| None;
        let to_field = |n: &str, s: Span| if tnames.iter().any(|t| t == n) { Some(var(&assoc_field_name(n), s)) } else { None };
        let rw = Rewrite { var: &none, con: &to_field, qualified: &nq };
        for (k, m) in c.members.iter().filter(|m| matches!(m, ClassMember::Type { .. })).enumerate() {
            let ClassMember::Type { name, constraints, .. } = m else { continue };
            let bs = type_bases(&name.name, constraints);
            if bs.is_empty() {
                continue;
            }
            // The class's parameters, a dictionary, and its types read from it.
            let mut cx = Cx::default();
            let mut pvals = Vec::new();
            for (n, kind) in &params {
                let kv = self.eval(&cx, kind);
                let l = cx.bind(n, kv, Mult::Zero);
                pvals.push(Val::var(l));
            }
            let d = cx.bind("$d", Val::TyCon(c.tid, pvals.clone().into()), Mult::Zero);
            for tn in &tnames {
                let Some(&acc) = self.assoc_defs.get(&(c.tid, tn.clone())) else { continue };
                let mut v = Val::Neutral(Head::Def(acc), Rc::new(Vec::new()));
                for p in &pvals {
                    v = crate::core::app(&self.g, v, p.clone(), Icit::Expl);
                }
                v = crate::core::app(&self.g, v, Val::var(d), Icit::Impl);
                cx.define(&assoc_field_name(tn), Val::Univ(0), v, Mult::Zero);
            }
            let n = params.len() + 1;
            let mut first: Option<(Val, &Expr)> = None;
            let mut tms = Vec::new();
            for b in bs {
                let t = self.elab_type(&mut cx, &rw.expr(b, &[]));
                if matches!(t, Tm::Error) {
                    continue;
                }
                let v = self.eval(&cx, &t);
                match &first {
                    Some((f, fe)) if unify(&self.g, cx.lvl(), f, &v).is_err() => {
                        let u = &name.name;
                        let (a, bt) = (self.src_text(fe.span), self.src_text(b.span));
                        self.err(
                            Diagnostic::error("E0372", format!("the value of `{u}` is given two types that don't agree: `{a}` and `{bt}`"), b.span)
                                .with_label(format!("it already has the type `{a}`"))
                                .with_help("each typing may refine the base type, as `u~Int, u~Nat` does, but they must have one base type"),
                        );
                        continue;
                    }
                    Some(_) => {}
                    None => first = Some((v.clone(), b)),
                }
                tms.push(quote(&self.g, n, &v));
            }
            if !tms.is_empty() {
                self.g.type_bases.insert((con, k), tms);
            }
        }
    }

    /// At an instance, whether its type for a class's type with a base type
    /// (#360) is the base, up to refinement (E0201 if not, reported by the
    /// base's own check, `own`); there, each of the base's predicates must
    /// hold of every value of it, `x`, a local of `cx` (E0450).
    #[allow(clippy::too_many_arguments)]
    pub fn class_type_base_holds(&mut self, cx: &Cx, lemma: &str, bases: &[Expr], x: &str, own: bool, span: Span) -> bool {
        let Some(l) = cx.locals.iter().rposition(|loc| loc.name.as_ref() == x) else { return false };
        // The base types at this instance: its types for the class's
        // parameters and for its types.
        let mut bcx = cx.clone();
        let n = self.diags.len();
        let tys: Vec<Val> = bases.iter().map(|b| {
            let t = self.elab_type(&mut bcx, b);
            self.eval(&bcx, &t)
        }).collect();
        // Its errors are the class's, reported there.
        self.diags.truncate(n);
        let Some(base) = tys.first().cloned() else { return false };
        let t = cx.locals[l].ty.clone();
        let (name, given) = self.class_type_checks.get(lemma).cloned().unwrap_or_default();
        let short = name.rsplit('.').next().unwrap_or(&name).to_string();
        // Its values must be the base's: a refinement inside it (`List U8`)
        // may not be dropped (`List Int`).
        let fits = unify(&self.g, cx.lvl(), &base, &t).is_ok() && (!own || self.refined_mismatch(cx, &base, &t, span).is_none());
        if !fits {
            if own {
                let b = self.show_written(cx, &base);
                self.err(
                    Diagnostic::error("E0201", format!("`{name}` must be `{b}`, or a refinement of it, but `{given}` is not"), span)
                        .with_label(format!("`{short}` is `{given}` here"))
                        .with_help(format!("give `{short}` the type `{b}`, or a refinement of it")),
                );
            }
            return false;
        }
        if !own {
            return true;
        }
        // Each base type's own refinement (`Nat`'s `n >= 0`), at the value.
        for base in &tys {
        let peeled = self.peel(base);
        if let Some((alias, args)) = self.refined_alias(&peeled) {
            let preds = self.alias_preds.get(&alias).cloned().unwrap_or_default();
            let mut names = self.alias_param_names(cx, alias, &args);
            if let Some(subj) = self.alias_subject.get(&alias) {
                names.push((subj.to_string(), x.to_string()));
            }
            for p in &preds {
                let mut env = args.clone();
                env.push(Val::var(l));
                let goal = self.inst_pred(p, env);
                let text = super::rename_words(&p.text, &names);
                self.oblige(cx, span, ObKind::ClassType { name: name.clone(), given: given.clone() }, text, goal, None);
            }
        }
        }
        true
    }

    /// A class's types (#133): for each, `C.Name`, the definition
    /// `\t {d~C t} -> d.$Name` of type `t~K -> {C t} -> Type`, `K` the
    /// kind of the class's parameter; with several parameters (#145),
    /// `\s h {d~C s h} -> d.$Name`.
    fn register_assoc(&mut self, c: &ClassDef) {
        let Some(&con) = self.g.tys[c.tid.0 as usize].ctors.first() else { return };
        let kind_of = |param: &str| {
            let arity = c
                .members
                .iter()
                .flat_map(|m| match m {
                    ClassMember::Fn { constraints, .. } | ClassMember::Lemma { constraints, .. } => constraints.as_slice(),
                    ClassMember::Type { .. } => &[],
                })
                .filter_map(|k| match k {
                    Constraint::Typed { ty, .. } => Some(applied_arity(ty, param)),
                    _ => None,
                })
                .max()
                .unwrap_or(0);
            let mut kind = Tm::Univ(0);
            for _ in 0..arity {
                kind = Tm::Pi(Rc::from("_"), Mult::Many, Icit::Expl, Rc::new(Tm::Univ(0)), Rc::new(kind));
            }
            kind
        };
        let kinds: Vec<Tm> = c.params.iter().map(|p| kind_of(p)).collect();
        let n = c.params.len();
        // Its types are the dictionary's first fields.
        for (k, t) in c.types().iter().enumerate() {
            let d = self.new_def(&format!("{}.{t}", c.name));
            // Under the parameters, parameter `i` is `Var(n - 1 - i)`.
            let dict = Tm::TyConApp(c.tid, (0..n).map(|i| Tm::Var(n - 1 - i)).collect());
            let mut ty = Tm::Pi(Rc::from("$d"), Mult::Many, Icit::Impl, Rc::new(dict), Rc::new(Tm::Univ(0)));
            let mut body = Tm::Lam(Rc::from("$d"), Mult::Many, Icit::Impl, Rc::new(Tm::Field(Rc::new(Tm::Var(0)), con, k)));
            for (p, kind) in c.params.iter().zip(&kinds).rev() {
                ty = Tm::Pi(Rc::from(p.as_str()), Mult::Zero, Icit::Expl, Rc::new(kind.clone()), Rc::new(ty));
                body = Tm::Lam(Rc::from(p.as_str()), Mult::Zero, Icit::Expl, Rc::new(body));
            }
            let info = &mut self.g.defs[d.0 as usize];
            info.ty = ty;
            info.body = Some(body);
            self.transparent.insert(d);
            self.assoc_defs.insert((c.tid, t.clone()), d);
        }
    }

    fn register_instance(&mut self, ix: usize, def: DefId, ids: &[Option<Sym>]) {
        let p = self.pending_insts[ix].clone();
        self.dict_defs.insert(def);
        self.g.well_known.dict_fns.insert(def);
        let class = match p.class {
            Some(t) => t,
            None => match self.resolve(&p.class_name, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => t,
                _ => return,
            },
        };
        // Each type: its type constructor and variables, or a variable.
        let mut pats = Vec::new();
        for head in &p.heads {
            let mut args = Vec::new();
            let mut h = head;
            while let ExprKind::App(f, a) = &h.kind {
                args.push(a);
                h = f;
            }
            args.reverse();
            let pos = |e: &Expr| match &e.kind {
                ExprKind::Var(v) => p.vars.iter().position(|x| x == v),
                _ => None,
            };
            let key = match &h.kind {
                ExprKind::Var(v) if args.is_empty() => {
                    let Some(k) = p.vars.iter().position(|x| x == v) else { return };
                    pats.push(InstPat::Var(k));
                    continue;
                }
                ExprKind::Tuple(xs) if xs.is_empty() => HeadKey::Unit,
                ExprKind::Tuple(xs) => {
                    let vs: Option<Vec<usize>> = xs.iter().map(pos).collect();
                    let Some(vs) = vs else { return };
                    pats.push(InstPat::Head(HeadKey::Pair, vs));
                    continue;
                }
                ExprKind::Con(n) => match self.resolve(n, true) {
                    Some(Sym::Ty(t)) => HeadKey::Ty(t),
                    Some(Sym::Def(_)) => {
                        self.err(
                            Diagnostic::error("E0281", format!("`instance {}` is for a type alias", p.text), head.span)
                                .with_help("write the instance for the type the alias stands for: the class at the alias uses it, where its signature shows that the values it gives are of the alias"),
                        );
                        return;
                    }
                    _ => return,
                },
                _ => return,
            };
            let vs: Option<Vec<usize>> = args.iter().map(|a| pos(a)).collect();
            let Some(vs) = vs else { return };
            pats.push(InstPat::Head(key, vs));
        }
        let Some(InstPat::Head(key, _)) = pats.first().cloned() else { return };
        // Rust's orphan rule (D136 b, RFC 2451), by package: the class is
        // this package's, or one of the types is, with no bare variable
        // before it (#145).
        let pkg = self.package_of(&self.cur);
        let class_pkg = self.package_of(&self.class_defs[&class].module);
        let pkg_of = |e: &Self, k: &HeadKey| match k {
            HeadKey::Ty(t) => e.package_of(&e.g.tys[t.0 as usize].module),
            HeadKey::Unit | HeadKey::Pair => "std".to_string(),
        };
        if pkg != class_pkg {
            let cname = self.class_defs[&class].name.clone();
            let local = pats.iter().position(|q| matches!(q, InstPat::Head(k, _) if pkg_of(self, k) == pkg));
            let var_before = pats.iter().take(local.unwrap_or(0)).position(|q| matches!(q, InstPat::Var(_)));
            match (local, var_before) {
                (Some(_), None) => {}
                (Some(l), Some(v)) => {
                    let shown = |e: &Expr| self.src_text(e.span).trim().to_string();
                    let (vt, lt) = (shown(&p.heads[v]), shown(&p.heads[l]));
                    self.err(
                        Diagnostic::error("E0282", format!("`instance {}` must be in the package of `{cname}` or of one of its types", p.text), p.heads[v].span)
                            .with_label(format!("`{vt}` comes before `{lt}`, this package's type"))
                            .with_help("an instance whose types begin with a type variable could overlap another package's; put this package's type before any variable"),
                    );
                    return;
                }
                (None, _) => {
                    let (msg, label, help) = if p.heads.len() == 1 {
                        (
                            format!("`instance {}` must be in the package of `{cname}` or of the type", p.text),
                            "neither is declared in this package",
                            "an instance goes with its class or its type, so there is only ever one (Rust's orphan rule); wrap the type in a record of your own to give it this instance",
                        )
                    } else {
                        (
                            format!("`instance {}` must be in the package of `{cname}` or of one of its types", p.text),
                            "none of them is declared in this package",
                            "an instance goes with its class or one of its types (Rust's orphan rule); wrap a type in a record of your own to give it this instance",
                        )
                    };
                    self.err(Diagnostic::error("E0282", msg, p.span).with_label(label).with_help(help));
                    return;
                }
            }
        }
        // `Debug` (#126): every type has the derived instance, which only
        // the type's own module, or the class's (`std.string`'s instance
        // for the prelude's `String`), may replace, with no context.
        let cdef = &self.class_defs[&class];
        let is_debug = cdef.module == "std.string" && cdef.name == "Debug";
        if is_debug {
            let ty_module = match key {
                HeadKey::Ty(t) => self.g.tys[t.0 as usize].module.to_string(),
                HeadKey::Unit | HeadKey::Pair => "std.prelude".to_string(),
            };
            let shown = self.src_text(p.heads[0].span).trim().to_string();
            if ty_module != self.cur && cdef.module != self.cur {
                self.err(
                    Diagnostic::error("E0283", format!("`instance {}` overlaps the derived instance of `{shown}`", p.text), p.span)
                        .with_label(format!("`{shown}` is declared in `{ty_module}`"))
                        .with_help(format!("every type has a derived `Debug`; only `{shown}`'s own module, `{ty_module}`, may replace it")),
                );
                return;
            }
            if !p.context.is_empty() {
                self.err(
                    Diagnostic::error("E0281", format!("`instance {}` can't have a context", p.text), p.span)
                        .with_help("`debug` works at every type without a clause; remove the context"),
                );
                return;
            }
        }
        // No two instances whose types can be the same (#145): at each
        // position the same type constructor, or a variable in either.
        let same = |a: &InstPat, b: &InstPat| match (a, b) {
            (InstPat::Head(x, _), InstPat::Head(y, _)) => x == y,
            _ => true,
        };
        if let Some(other) = self.instances.get(&(class, key)).and_then(|v| v.iter().find(|o| o.pats.iter().zip(&pats).all(|(a, b)| same(a, b)))) {
            let (om, os) = (other.module.clone(), other.span);
            let line = self.sources.get(&om).map(|f| f.line_col(os.start).0).unwrap_or(0);
            let help = if p.heads.len() == 1 {
                "a type has one instance of each class; give the other order through a wrapper type, or `sort_as`/`sort_by`"
            } else {
                "no two instances of a class may match the same types; make one of them for other types"
            };
            self.err(
                Diagnostic::error("E0283", format!("`instance {}` overlaps another instance", p.text), p.span)
                    .with_label(format!("`{}` is already declared at {om}:{line}", other.text))
                    .with_help(help),
            );
            return;
        }
        let context: Vec<(TyId, Vec<usize>)> = p
            .context
            .iter()
            .filter_map(|(c, vs)| match self.resolve(c, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => {
                    Some((t, vs.iter().map(|v| p.vars.iter().position(|x| x == v)).collect::<Option<Vec<_>>>()?))
                }
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
        if let (true, HeadKey::Ty(t), Some(f)) = (is_debug, key, members.get("debug")) {
            self.g.well_known.debug_insts.push((t, *f));
        }
        self.instances.entry((class, key)).or_default().push(InstInfo {
            class,
            def,
            module: self.cur.clone(),
            span: p.span,
            n_vars: p.vars.len(),
            pats,
            context,
            members,
            text: p.text.clone(),
        });
    }

    /// What is known of `ty`: its type constructor and arguments.
    fn shape(&self, lvl: usize, ty: &Val) -> Shape {
        match self.force(ty) {
            // Without its header's dictionaries (#385): an instance's head
            // names its parameters only.
            Val::TyCon(t, args) => {
                let ti = &self.g.tys[t.0 as usize];
                Shape::Known(HeadKey::Ty(t), args[..args.len().min(ti.params.len() - ti.dicts)].to_vec())
            }
            // A type constructor not applied to its last argument (`List`
            // for `Functor`, M25): `\y -> T … y`.
            Val::Lam(_, _, _, c) => {
                let y = Val::var(lvl + 1000);
                match self.force(&apply_closure(&self.g, &c, y)) {
                    Val::TyCon(t, args) if args.last().is_some_and(|a| matches!(a, Val::Neutral(Head::Var(v), sp) if *v == lvl + 1000 && sp.is_empty())) => {
                        Shape::Known(HeadKey::Ty(t), args[..args.len() - 1].to_vec())
                    }
                    _ => Shape::Other,
                }
            }
            // `()`, or a tuple: a pair of its first part and the rest.
            Val::TupleTy(xs) => {
                let xs = crate::core::flat_parts(&self.g, &xs, true);
                match xs.len() {
                    0 => Shape::Known(HeadKey::Unit, Vec::new()),
                    1 => Shape::Other,
                    2 => Shape::Known(HeadKey::Pair, xs.to_vec()),
                    _ => Shape::Known(HeadKey::Pair, vec![xs[0].clone(), Val::TupleTy(xs[1..].into())]),
                }
            }
            Val::Neutral(Head::Meta(_), _) => Shape::Unknown,
            _ => Shape::Other,
        }
    }

    /// A dictionary for `class` at `tys`, as a term at level `lvl`: one in
    /// scope, or an instance's, with its context found the same way. An
    /// instance is chosen once the types are known wherever it names a type
    /// constructor (#145); until then the request waits.
    fn find_dict(&mut self, req: &InstReq, class: TyId, tys: &[Val], depth: usize) -> Result<Tm, String> {
        if depth > 32 {
            return Err("instances nested too deeply".into());
        }
        let asked: Vec<Val> = tys.iter().map(|t| force_meta(&self.g, t.clone())).collect();
        let tys: Vec<Val> = tys.iter().map(|t| self.force(t)).collect();
        let shown: Vec<String> = tys.iter().map(|t| format!("{:?}", quote(&self.g, req.lvl, t))).collect();
        let shapes: Vec<Shape> = tys.iter().map(|t| self.shape(req.lvl, t)).collect();
        // A known type's dictionary is its instance's (coherence); one in
        // scope is used for types that aren't all known.
        let concrete = shapes.iter().all(|s| matches!(s, Shape::Known(..)));
        for (l, c, ts) in req.given.iter().filter(|_| !concrete) {
            if *c == class && ts.len() == tys.len() && ts.iter().zip(&shown).all(|(t, s)| format!("{:?}", quote(&self.g, req.lvl, &self.force(t))) == *s) {
                return Ok(Tm::Var(req.lvl - l - 1));
            }
        }
        // A class's type read from a dictionary not known (`Seq.Elem s`):
        // a clause declared on it is a field of that dictionary (#176).
        if let Some(t) = self.clause_of_class_type(req.lvl, class, &tys) {
            return Ok(t);
        }
        // One in scope that may still be meant, once the unknown types are known.
        let unknown = shapes.iter().any(|s| matches!(s, Shape::Unknown));
        if unknown && !concrete {
            let maybe = req.given.iter().any(|(_, c, ts)| {
                *c == class
                    && ts.len() == tys.len()
                    && ts.iter().zip(&shown).zip(&shapes).all(|((t, s), sh)| matches!(sh, Shape::Unknown) || format!("{:?}", quote(&self.g, req.lvl, &self.force(t))) == *s)
            });
            if maybe {
                return Err("unknown".into());
            }
        }
        let key = match shapes.first() {
            Some(Shape::Known(k, _)) => *k,
            Some(Shape::Unknown) => return Err("unknown".into()),
            _ => return Err("none".into()),
        };
        // An instance is chosen once the use's types are known wherever it
        // names a type constructor; never because the others are ruled out,
        // as which instances are visible depends on the modules loaded (#145).
        let cands = self.instances.get(&(class, key)).cloned().unwrap_or_default();
        let mut undecided = false;
        let mut chosen = None;
        for inst in cands {
            let mut fits = Some(true);
            for (p, s) in inst.pats.iter().zip(&shapes) {
                match (p, s) {
                    (InstPat::Var(_), _) => {}
                    (InstPat::Head(k, vs), Shape::Known(k2, args)) if k == k2 && args.len() >= vs.len() => {}
                    (InstPat::Head(..), Shape::Unknown) => fits = fits.map(|_| false),
                    _ => fits = None,
                }
            }
            match fits {
                Some(true) => chosen = Some(inst),
                Some(false) => undecided = true,
                None => {}
            }
        }
        let inst = match chosen {
            Some(i) => i,
            None if undecided => return Err("unknown".into()),
            None => return Err("none".into()),
        };
        // What this module's proofs may now depend on (#272).
        if inst.module != self.cur {
            self.instance_deps.entry(self.cur.clone()).or_default().insert(inst.module.clone());
        }
        // The instance's variables, from the types.
        let mut bound: Vec<Option<Val>> = vec![None; inst.n_vars];
        for ((p, s), ty) in inst.pats.iter().zip(&shapes).zip(&tys) {
            match (p, s) {
                (InstPat::Var(v), _) => bound[*v] = Some(ty.clone()),
                (InstPat::Head(_, vs), Shape::Known(_, args)) => {
                    let args = &args[args.len() - vs.len()..];
                    for (v, a) in vs.iter().zip(args) {
                        bound[*v] = Some(a.clone());
                    }
                }
                _ => return Err("unknown".into()),
            }
        }
        let Some(args) = bound.into_iter().collect::<Option<Vec<Val>>>() else { return Err("none".into()) };
        let mut t = Tm::Def(inst.def);
        for a in &args {
            t = Tm::App(Rc::new(t), Rc::new(quote(&self.g, req.lvl, a)), Icit::Impl, Mult::Zero);
        }
        // The dictionary's parameters so far, as values: the variables,
        // then the context's dictionaries.
        let lvl_env = Rc::new((0..req.lvl).map(Val::var).collect::<Vec<_>>());
        let mut env = args.clone();
        for (c, vs) in &inst.context {
            let ctys: Vec<Val> = vs.iter().map(|v| args[*v].clone()).collect();
            let d = match self.find_dict(req, *c, &ctys, depth + 1) {
                Ok(d) => d,
                Err(e) => {
                    // The innermost missing one is what to report.
                    if e == "none" && self.ctx_missing.is_none() {
                        self.ctx_missing = Some((*c, ctys, inst.text.clone()));
                    }
                    return Err(e);
                }
            };
            env.push(eval(&self.g, &lvl_env, &d));
            t = Tm::App(Rc::new(t), Rc::new(d), Icit::Impl, Mult::Many);
        }
        // Its head's types' clauses (#385), implied in its context: found
        // the same way, at the types asked for.
        for ty in self.inst_implied.get(&inst.def).cloned().unwrap_or_default() {
            let Val::TyCon(c, ctys) = self.force(&eval(&self.g, &Rc::new(env.clone()), &ty)) else { return Err("none".into()) };
            let d = self.find_dict(req, c, &ctys, depth + 1)?;
            env.push(eval(&self.g, &lvl_env, &d));
            t = Tm::App(Rc::new(t), Rc::new(d), Icit::Impl, Mult::Many);
        }
        // Its class's types are kept in the dictionary as descriptors, built
        // from the instance's types (#170): a use of the function building it.
        if !req.in_spec && !args.is_empty() {
            self.dict_insts.push(Inst { caller: req.owner, callee: inst.def, args: args.clone(), lvl: req.lvl, names: req.names.clone(), span: req.span });
        }
        // Through a refinement alias, where the instance names the type
        // constructor (`Make Nat` is `Make Int`'s): checked once the
        // module's bodies are (#226).
        if let (false, Some(cx)) = (req.in_spec, &req.cx) {
            for (k, (p, a)) in inst.pats.iter().zip(&asked).enumerate() {
                if matches!(p, InstPat::Head(..)) && self.refined_alias(a).is_some() {
                    let meta = match (depth, force_meta(&self.g, req.meta.clone())) {
                        (0, Val::Neutral(Head::Meta(m), _)) => Some(m),
                        _ => None,
                    };
                    self.alias_dicts.push(AliasDict {
                        meta,
                        cx: cx.clone(),
                        span: req.span,
                        owner: req.owner,
                        class,
                        tys: asked.clone(),
                        pos: k,
                        dict: t.clone(),
                        members: inst.members.clone(),
                        inst_text: inst.text.clone(),
                    });
                }
            }
        }
        // Using an instance of this module: a call, for termination (D136).
        if inst.module == self.cur && !req.in_spec {
            if let Some(caller) = req.owner {
                self.calls.push(CallRec { caller, callee: inst.def, args: Vec::new(), same: Vec::new(), span: req.span, conds: Vec::new() });
            }
        }
        Ok(t)
    }

    /// The dictionary for `class` at `tys`, if that is one type read from a
    /// dictionary (`d.$Elem`) whose class declares the clause on it (#176):
    /// the field of `d` holding it.
    fn clause_of_class_type(&self, lvl: usize, class: TyId, tys: &[Val]) -> Option<Tm> {
        let [Val::Neutral(h, sp)] = tys else { return None };
        let Some(Elim::Field(c, i)) = sp.last() else { return None };
        if matches!(h, Head::Meta(_)) || !self.g.is_type_field(*c, *i) {
            return None;
        }
        let cd = self.class_defs.get(&self.g.cons[c.0 as usize].ty)?;
        let (_, _, field) = cd.clauses.iter().find(|(t, k, _)| *t == *i && *k == class)?;
        let base = Val::Neutral(h.clone(), Rc::new(sp[..sp.len() - 1].to_vec()));
        Some(Tm::Field(Rc::new(quote(&self.g, lvl, &base)), *c, *field))
    }

    /// The instances a request still waiting could mean, as written
    /// (`Hole Plain Int`): those whose types it may match once known.
    fn undecided(&self, r: &InstReq) -> Vec<String> {
        let shapes: Vec<Shape> = r.tys.iter().map(|t| self.shape(r.lvl, t)).collect();
        let Some(Shape::Known(key, _)) = shapes.first() else { return Vec::new() };
        let fits = |inst: &InstInfo| {
            inst.pats.iter().zip(&shapes).all(|(p, s)| match (p, s) {
                (InstPat::Var(_), _) | (InstPat::Head(..), Shape::Unknown) => true,
                (InstPat::Head(k, vs), Shape::Known(k2, args)) => k == k2 && args.len() >= vs.len(),
                _ => false,
            })
        };
        self.instances.get(&(r.class, *key)).map(|v| v.iter().filter(|i| fits(i)).map(|i| i.text.clone()).collect()).unwrap_or_default()
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
        let shown: Vec<String> = r
            .tys
            .iter()
            .map(|t| {
                let s = crate::core::show_marked(&self.g, &r.names, &quote(&self.g, r.lvl, t));
                if s.contains(' ') {
                    format!("({s})")
                } else {
                    s
                }
            })
            .collect();
        self.err(
            Diagnostic::error("E0225", format!("`{name} {}` depends on itself", shown.join(" ")), r.span)
                .with_help("an instance's type stands for the type it is given, so this would never end; give the type itself"),
        );
        true
    }

    /// The instance whose member's signature is `decl` (an index into the
    /// desugared module), if it is one (#146).
    pub fn sig_inst_of(&self, decl: usize) -> Option<SigInst> {
        let (cname, heads) = self.member_heads.get(&decl)?;
        let class = match self.resolve(cname, true) {
            Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => t,
            _ => return None,
        };
        let mut out = Vec::new();
        for head in heads {
            let mut vars = Vec::new();
            let mut h = head;
            while let ExprKind::App(f, a) = &h.kind {
                if let ExprKind::Var(v) = &a.kind {
                    vars.push(v.clone());
                }
                h = f;
            }
            vars.reverse();
            let key = match &h.kind {
                ExprKind::Var(v) => {
                    out.push((None, vec![v.clone()]));
                    continue;
                }
                ExprKind::Tuple(xs) if xs.is_empty() => HeadKey::Unit,
                ExprKind::Tuple(xs) => {
                    vars = xs.iter().filter_map(|x| if let ExprKind::Var(v) = &x.kind { Some(v.clone()) } else { None }).collect();
                    HeadKey::Pair
                }
                ExprKind::Con(n) => match self.resolve(n, true) {
                    Some(Sym::Ty(t)) => HeadKey::Ty(t),
                    _ => return None,
                },
                _ => return None,
            };
            out.push((Some(key), vars));
        }
        Some(SigInst { class, heads: out })
    }

    /// Solve `r`, whose types aren't known, with the instance whose
    /// member's signature it is in: its types' variables are locals there.
    fn use_fallback(&mut self, r: &InstReq) -> bool {
        let Some(f) = &r.fallback else { return false };
        if f.heads.len() != r.tys.len() {
            return false;
        }
        for ((key, vars), ty) in f.heads.iter().zip(&r.tys) {
            let mut args = Vec::new();
            for v in vars {
                let Some(l) = r.names.iter().rposition(|n| **n == **v) else { return false };
                args.push(Val::var(l));
            }
            let head = match key {
                None => args.remove(0),
                Some(HeadKey::Ty(t)) if self.g.arity_ty(*t) == args.len() => Val::TyCon(*t, args.into()),
                Some(HeadKey::Unit) => Val::TupleTy(Rc::new([])),
                Some(HeadKey::Pair) if args.len() == 2 => Val::TupleTy(args.into()),
                _ => return false,
            };
            if unify(&self.g, r.lvl, ty, &head).is_err() {
                return false;
            }
        }
        match self.find_dict(r, r.class, &r.tys, 0) {
            Ok(t) => {
                let env = Rc::new((0..r.lvl).map(Val::var).collect::<Vec<_>>());
                let v = eval(&self.g, &env, &t);
                unify(&self.g, r.lvl, &r.meta, &v).is_ok()
            }
            Err(_) => false,
        }
    }

    /// Whether the type `e` writes may have a type with class clauses in
    /// its header (#385): one named, or one in an alias named.
    pub fn names_type_with_clauses(&self, e: &Expr) -> bool {
        let names = std::cell::RefCell::new(Vec::new());
        let none = |_: &str, _: Span| None;
        let con = |n: &str, _: Span| {
            names.borrow_mut().push(self.resolve(n, true));
            None
        };
        let qualified = |m: &str, n: &str, _: Span| {
            names.borrow_mut().push(self.resolve_qualified(m, n, true));
            None
        };
        Rewrite { var: &none, con: &con, qualified: &qualified }.expr(e, &[]);
        let mut seen = HashSet::new();
        names.into_inner().into_iter().flatten().any(|s| self.sym_has_clauses(s, &mut seen))
    }

    fn sym_has_clauses(&self, s: Sym, seen: &mut HashSet<DefId>) -> bool {
        match s {
            Sym::Ty(t) => self.g.tys[t.0 as usize].dicts > 0,
            Sym::Def(d) if self.alias_subject.contains_key(&d) && seen.insert(d) => {
                self.g.defs[d.0 as usize].body.as_ref().is_some_and(|b| self.tm_has_clauses(b, seen))
            }
            _ => false,
        }
    }

    fn tm_has_clauses(&self, t: &Tm, seen: &mut HashSet<DefId>) -> bool {
        match t {
            Tm::TyCon(id) | Tm::TyConApp(id, _) if self.g.tys[id.0 as usize].dicts > 0 => true,
            Tm::Def(d) => self.sym_has_clauses(Sym::Def(*d), seen),
            _ => t.any_sub(|x, _| self.tm_has_clauses(x, seen)),
        }
    }

    /// A type's header's dictionary asked for in a signature (#385), at level
    /// `lvl`: its type, if it is an implied clause there, one that mentions
    /// the signature's names (and no unknowns, nor names bound inside the
    /// type) and that nothing finds: neither a dictionary in scope nor an
    /// instance. Else the dictionary is wanted as anywhere.
    pub fn implied_clause(&mut self, r: &InstReq, lvl: usize) -> Option<Tm> {
        if !matches!(self.force(&r.meta), Val::Neutral(Head::Meta(_), _)) {
            return None;
        }
        let tys: Vec<Val> = r.tys.iter().map(|t| self.force(t)).collect();
        let ty = zonk_metas(&self.g, r.lvl, &quote(&self.g, r.lvl, &Val::TyCon(r.class, tys.into())));
        if has_meta(&ty) {
            return None;
        }
        let mut free = std::collections::BTreeSet::new();
        free_vars(&ty, 0, &mut free);
        let inside = r.lvl.checked_sub(lvl)?;
        if free.is_empty() || free.iter().any(|i| *i < inside) {
            return None;
        }
        match self.find_dict(r, r.class, &r.tys, 0) {
            Err(why) if why != "unknown" => Some(rename_free(&ty, 0, &|i| i - inside)),
            _ => None,
        }
    }

    /// Find the dictionaries asked for so far. With `last`, report those
    /// whose type still isn't known.
    pub fn solve_instances(&mut self, last: bool) {
        // Before reporting, settle what can be: one request's dictionary can
        // make another's type known (`show (made 1)`: `Make Int` reduces
        // `Made`, then `Show Int` is known), whatever order they came in.
        if last {
            loop {
                let before = self.inst_reqs.len();
                self.solve_instances(false);
                if self.inst_reqs.len() == before {
                    break;
                }
            }
        }
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
            self.ctx_missing = None;
            match self.find_dict(&r, r.class, &r.tys, 0) {
                Ok(t) => {
                    if self.assoc_cycle(&r, &t) {
                        continue;
                    }
                    let env = Rc::new((0..r.lvl).map(Val::var).collect::<Vec<_>>());
                    let v = eval(&self.g, &env, &t);
                    let _ = unify(&self.g, r.lvl, &r.meta, &v);
                }
                Err(why) if why == "unknown" && !last => self.inst_reqs.push(r),
                // In an instance's signature, a class's function whose type
                // its arguments don't tell is the instance's own (#146).
                Err(why) if why == "unknown" && self.use_fallback(&r) => {}
                Err(why) => {
                    // An unknown type in a reported mismatch: that error's (D141 c).
                    if why == "unknown" && r.tys.iter().any(|t| self.unknowns(r.lvl, t).iter().any(|m| self.blamed.contains(m))) {
                        continue;
                    }
                    // An instance chosen whose context isn't there: that is
                    // what is missing (`Display Point` for `Hole Format a`).
                    let (class, tys, via) = match self.ctx_missing.take().filter(|_| why == "none") {
                        Some((c, ts, text)) => (c, ts, Some(text)),
                        None => (r.class, r.tys.clone(), None),
                    };
                    let cname = self.class_defs.get(&class).map(|c| c.name.clone()).unwrap_or_default();
                    let shown: Vec<String> = tys
                        .iter()
                        .map(|t| match self.force(t) {
                            // `\y -> List y` is `List`.
                            Val::Lam(_, _, _, c) => match self.force(&apply_closure(&self.g, &c, Val::var(r.lvl))) {
                                Val::TyCon(t, args) if args.len() == 1 => self.g.tys[t.0 as usize].name.to_string(),
                                _ => crate::core::show_marked(&self.g, &r.names, &quote(&self.g, r.lvl, t)),
                            },
                            _ => crate::core::show_marked(&self.g, &r.names, &quote(&self.g, r.lvl, t)),
                        })
                        .collect();
                    let args: Vec<String> = shown.iter().map(|s| if s.contains(' ') { format!("({s})") } else { s.clone() }).collect();
                    let clause = format!("{cname} {}", args.join(" "));
                    let several = tys.len() > 1;
                    let param = tys.iter().zip(&shown).find(|(t, _)| matches!(self.force(t), Val::Neutral(Head::Var(_), _)));
                    let needs = match (&via, r.of_type) {
                        (Some(text), _) => format!("needs `{clause}`, for `instance {text}`"),
                        // A type's header's (#385).
                        (None, Some(t)) => format!("`{}` needs `{clause}`", self.g.tys[t.0 as usize].name),
                        (None, None) => format!("needs `{clause}`"),
                    };
                    let could = if why == "unknown" { self.undecided(&r) } else { Vec::new() };
                    let d = if why == "unknown" {
                        let d = Diagnostic::error("E0285", format!("can't tell which instance of `{cname}` to use: the type isn't known here"), r.span);
                        // Several instances could match: the label names them (#145).
                        let d = if could.len() > 1 { d.with_label(format!("`{clause}` could be {}", joined(&could, "or"))) } else { d };
                        d.with_help("give the type, e.g. with a constraint `x~List Int` in the signature")
                    } else if let Some((_, p)) = param {
                        // In an instance, its members have the class's
                        // signatures: the clause goes in its context.
                        let help = match r.owner.or(r.instance_sig).and_then(|o| self.instance_header(o)) {
                            Some(h) if h.contains(" : ") => format!("add `{clause}` to the instance's context: `{h}, {clause}`"),
                            Some(h) => format!("add `{clause}` to the instance's context: `{h} : {clause}`"),
                            None => format!("add `{clause}` to the function's signature"),
                        };
                        Diagnostic::error("E0284", format!("no instance of `{cname}` for {}", joined(&shown, "and")), r.span)
                            .with_label(format!("`{p}` is a type parameter"))
                            .with_help(help)
                    } else if several {
                        Diagnostic::error("E0284", format!("no instance of `{cname}` for {}", joined(&shown, "and")), r.span)
                            .with_label(needs)
                            .with_help(format!("declare `instance {cname} …` for these types, beside the class or the first type"))
                    } else {
                        let shown = &shown[0];
                        // A class of another package: only beside the type.
                        let theirs = self.class_defs.get(&class).is_some_and(|c| self.package_of(&c.module) != self.package_of(&self.cur));
                        let where_ = if theirs { "beside the type" } else { "beside the class or the type" };
                        Diagnostic::error("E0284", format!("no instance of `{cname}` for `{shown}`"), r.span)
                            .with_label(needs)
                            .with_help(format!("declare `instance {cname} …` for this type, {where_}"))
                    };
                    self.err(d);
                    // What follows from the dictionary not being found
                    // follows from this error (D141 c).
                    if let Val::Neutral(Head::Meta(m), _) = force_meta(&self.g, r.meta.clone()) {
                        self.blamed.insert(m);
                    }
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
            self.waiting.push((lvl, expected.clone(), actual.clone(), span, names.to_vec(), true));
        }
    }

    /// Does `t` read a class's type from an instance's dictionary whose
    /// body isn't elaborated yet?
    fn on_pending_dict(&self, t: &Tm) -> bool {
        if let (Tm::Def(d), args) = t.spine() {
            if let Some(n) = self.g.assoc_def(*d).map(|(_, _, n)| n).filter(|n| args.len() == n + 1) {
                if let Tm::Def(dd) = args[n].head() {
                    if self.dict_defs.contains(dd) && self.g.defs[dd.0 as usize].body.is_none() {
                        return true;
                    }
                }
            }
        }
        t.any_sub(|x, _| self.on_pending_dict(x))
    }

    /// At the end of a module: the comparisons that waited for its
    /// instances' dictionaries.
    pub fn retry_late(&mut self) {
        self.waiting.append(&mut self.waiting_late);
        self.retry_waiting(true);
        // Still waiting: a dictionary never elaborated (its instance has
        // errors, reported there).
        self.waiting_late.clear();
    }

    /// `t` with each class's type at a known instance replaced by the
    /// instance's (#133): `NoOptions` for `Display.Options Int`, in messages.
    pub fn reduce_assoc(&self, lvl: usize, t: &Tm) -> Tm {
        if let (Tm::Def(d), args) = t.spine() {
            if self.g.assoc_def(*d).is_some_and(|(_, _, n)| args.len() == n + 1) {
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
            self.waiting.push((l, a, b, self.name_span, names, false));
        }
        for (l, a, b, span, names, directed) in std::mem::take(&mut self.waiting) {
            let mut r = unify(&self.g, l, &a, &b);
            // Modulo the type equations in scope (#209).
            if r.is_err() && !self.givens.is_empty() {
                r = unify(&self.g, l, &self.rep_deep(l, &a), &self.rep_deep(l, &b));
            }
            let again = {
                let mut p = self.g.postponed.borrow_mut();
                let again = !p.is_empty();
                p.clear();
                again
            };
            match r {
                Ok(()) if again => {
                    if !last {
                        self.waiting.push((l, a, b, span, names, directed));
                    }
                }
                // Expected and found: which way a value may go between a
                // class's type with a base type and others (#360), now
                // that its dictionary is known.
                Ok(()) if directed && (self.based_inside(&a, l) || self.based_inside(&b, l)) => {
                    let mut cx = Cx::default();
                    for n in &names {
                        cx.bind(n, Val::Error, Mult::Zero);
                    }
                    match self.refined_mismatch(&cx, &a, &b, span) {
                        Some(g) => self.report_gained(&cx, &a, &b, &g, span, "this expression"),
                        None => self.check_based(&cx, &a, Some(&b), span),
                    }
                }
                Ok(()) => {}
                // A dictionary whose body isn't elaborated yet (an instance's
                // own, in its members' signatures): compared again at the
                // end of the module.
                Err(_) if self.on_pending_dict(&quote(&self.g, l, &a)) || self.on_pending_dict(&quote(&self.g, l, &b)) => {
                    self.waiting_late.push((l, a, b, span, names, directed));
                }
                Err(_) => {
                    let e = crate::core::show_marked(&self.g, &names, &self.reduce_assoc(l, &quote(&self.g, l, &a)));
                    let f = crate::core::show_marked(&self.g, &names, &self.reduce_assoc(l, &quote(&self.g, l, &b)));
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
        let Val::TyCon(tid, tys) = self.force(dom) else { return };
        if !self.class_defs.contains_key(&tid) || tys.is_empty() {
            return;
        }
        let mut given = Vec::new();
        for (l, loc) in cx.locals.iter().enumerate() {
            if let Val::TyCon(c, a) = self.force(&loc.ty) {
                if self.class_defs.contains_key(&c) && !a.is_empty() {
                    given.push((l, c, a.to_vec()));
                }
            }
        }
        self.inst_reqs.push(InstReq {
            meta: meta.clone(),
            class: tid,
            tys: tys.to_vec(),
            lvl: cx.lvl(),
            names: cx.names(),
            span,
            owner: self.cur_fn,
            in_spec: self.in_spec > 0,
            given,
            assoc: None,
            fallback: self.sig_inst.clone().filter(|f| f.class == tid),
            cx: (self.in_spec == 0).then(|| Rc::new(cx.clone())),
            of_type: None,
            instance_sig: self.instance_sig,
        });
    }
}

impl Elab {
    /// An instance's function with a signature of its own (#225): the same
    /// parameters and types as the class's signature at the instance, up
    /// to refinement (else E0365), and a refinement of it (E0371, by the
    /// prover): the class's preconditions imply the instance's, and the
    /// instance's postconditions, where the class's preconditions hold,
    /// imply the class's. When the shapes differ, the class's type, for
    /// the function as the dictionary has it: one error, not two.
    /// When its signature has errors already, it is only given the class's
    /// type.
    pub fn check_inst_refines(&mut self, k: usize, d: &Decl, sig: &super::decls::Sig, failed: bool) -> Option<Tm> {
        let r = self.inst_refines.get(&k)?;
        let DeclKind::Fn { name, params, result, constraints, .. } = &d.kind else { return None };
        let (class, member, declared) = (r.class.clone(), r.member.clone(), r.declared.clone());
        let (cresult, ccs) = (r.result.clone(), r.constraints.clone());
        let diags_before = self.diags.len();
        let csig = self.signature(params, cresult.as_ref(), &ccs);
        // The class's signature was checked where it was declared.
        self.diags.truncate(diags_before);
        let note = format!("class `{class}` declares `{declared}`");
        // Its signature, without the instance's context (in its header).
        let header = constraints.iter().fold(name.span, |s, c| {
            let end = match c {
                Constraint::Typed { ty, .. } => ty.span,
                Constraint::Pred(e) | Constraint::Named(_, e) => e.span,
            };
            if end.start > s.start {
                s.to(end)
            } else {
                s
            }
        });
        // Where a parameter's (or the result's) type is written.
        let type_span = |n: &str| {
            constraints
                .iter()
                .find_map(|c| match c {
                    Constraint::Typed { name, ty, .. } if name.name == n => Some(ty.span),
                    _ => None,
                })
                .unwrap_or(header)
        };
        // The same shape: binder by binder, then the result.
        let shape = |e: &Self, sig: &super::decls::Sig| e.eval(&Cx::default(), &Self::pi_of(&sig.binders, sig.result.clone()));
        let (mut mine, mut theirs) = (shape(self, sig), shape(self, &csig));
        let mut lvl = 0;
        let mut cx = Cx::default();
        let class_ty = Self::pi_of(&csig.binders, csig.result.clone());
        if failed {
            return Some(class_ty);
        }
        let rname = result.as_ref().map_or("the result".to_string(), |r| r.name.clone());
        loop {
            let (a, b) = (force_meta(&self.g, mine.clone()), force_meta(&self.g, theirs.clone()));
            match (&a, &b) {
                (Val::Pi(x, m1, i1, d1, c1), Val::Pi(_, m2, i2, d2, c2)) => {
                    let explicit = *i1 == Icit::Expl;
                    if m1 != m2 || i1 != i2 || unify(&self.g, lvl, d1, d2).is_err() {
                        let (span, what) = if explicit {
                            (type_span(x), format!("parameter `{x}`"))
                        } else {
                            (header, "type parameters and class clauses".to_string())
                        };
                        let (mine_s, theirs_s) = (self.show_val(&cx, d1), self.show_val(&cx, d2));
                        let shown = |m: &Mult, s: &str| match m {
                            Mult::Zero => format!("ghost {s}"),
                            Mult::One => format!("own {s}"),
                            _ => s.to_string(),
                        };
                        let mut diag = Diagnostic::error("E0365", format!("`{member}`'s {what} doesn't match class `{class}`"), span);
                        if explicit {
                            diag = diag
                                .with_label(format!("`{}` here, `{}` in the class", shown(m1, &mine_s), shown(m2, &theirs_s)))
                                .with_help("an instance's signature has the class's types at the instance's type; it may only refine them");
                        }
                        self.err(diag.with_note(note));
                        return Some(class_ty);
                    }
                    cx.bind(x, (**d1).clone(), *m1);
                    mine = apply_closure(&self.g, c1, Val::var(lvl));
                    theirs = apply_closure(&self.g, c2, Val::var(lvl));
                    lvl += 1;
                }
                (Val::Pi(..), _) | (_, Val::Pi(..)) => {
                    let diag = Diagnostic::error("E0365", format!("`{member}` doesn't take the class's parameters and class clauses"), header)
                        .with_help("an instance's signature has the class's parameters, types and class clauses, at the instance's type");
                    self.err(diag.with_note(note));
                    return Some(class_ty);
                }
                _ => {
                    if unify(&self.g, lvl, &a, &b).is_err() {
                        let (mine_s, theirs_s) = (self.show_val(&cx, &a), self.show_val(&cx, &b));
                        let span = result.as_ref().map_or(header, |r| type_span(&r.name));
                        self.err(
                            Diagnostic::error("E0365", format!("`{member}`'s result doesn't match class `{class}`"), span)
                                .with_label(format!("`{rname}` is `{mine_s}` here, `{theirs_s}` in the class"))
                                .with_help("an instance's signature has the class's types at the instance's type; it may only refine them")
                                .with_note(note),
                        );
                        return Some(class_ty);
                    }
                    break;
                }
            }
        }
        // The class's parameters, as a caller through the class has them.
        let mut cx = csig.cx.clone();
        let mut env = cx.env.to_vec();
        let rlvl = cx.lvl();
        env.push(Val::var(rlvl));
        let pres = |s: &super::decls::Sig| s.preds.iter().filter(|p| !p.is_post).cloned().collect::<Vec<_>>();
        let posts = |s: &super::decls::Sig| s.preds.iter().filter(|p| p.is_post).cloned().collect::<Vec<_>>();
        let kind_at = |pre: bool, at: Option<(String, String, String)>| ObKind::Refines { class: class.clone(), member: member.clone(), pre, declared: declared.clone(), at };
        let kind = |pre: bool| kind_at(pre, None);
        let saved = self.cur_fn.take();
        for p in pres(&csig) {
            let v = self.inst_pred(&p, env.clone());
            cx.assume(v);
        }
        // Each of the instance's preconditions follows from the class's.
        for p in pres(sig) {
            let goal = self.inst_pred(&p, env.clone());
            let span = if p.span.start < p.span.end { p.span } else { header };
            self.oblige(&cx, span, kind(true), p.text.clone(), goal, None);
        }
        // Refinements inside its parameters' types (a refinement at the
        // top is a precondition, above): every value of the class's type
        // is one of the instance's (§7.5).
        for (i, ((x, _, icit, ity), (_, _, _, cty))) in sig.binders.iter().zip(&csig.binders).enumerate() {
            if *icit != Icit::Expl || i > rlvl {
                continue;
            }
            let benv = Rc::new(env[..i].to_vec());
            let (iv, cv) = (eval(&self.g, &benv, ity), eval(&self.g, &benv, cty));
            let at = (x.to_string(), self.show_val(&cx, &iv), self.show_val(&cx, &cv));
            let k = kind_at(true, Some(at.clone()));
            let span = type_span(x);
            if let Some(g) = self.refined_implies_inside(&cx, &iv, &cv, span, k) {
                self.inside_gained(&g, &at, true, &class, &member, span, &note);
            }
        }
        // Its result, of the instance's type: with the instance's
        // preconditions (which hold) and postconditions, the class's
        // postconditions hold.
        let rty = self.eval(&cx, &sig.result);
        let crty = self.eval(&cx, &csig.result);
        cx.bind(&rname, rty.clone(), Mult::Zero);
        for p in pres(sig).iter().chain(posts(sig).iter()) {
            let v = self.inst_pred(p, env.clone());
            cx.assume(v);
        }
        for p in posts(&csig) {
            let goal = self.inst_pred(&p, env.clone());
            self.oblige(&cx, header, kind(false), p.text.clone(), goal, None);
        }
        // And the refinements inside its type: every value of the
        // instance's result type is one of the class's.
        let at = (rname.clone(), self.show_val(&cx, &rty), self.show_val(&cx, &crty));
        let k = kind_at(false, Some(at.clone()));
        let span = result.as_ref().map_or(header, |r| type_span(&r.name));
        if let Some(g) = self.refined_implies_inside(&cx, &crty, &rty, span, k) {
            self.inside_gained(&g, &at, false, &class, &member, span, &note);
        }
        self.cur_fn = saved;
        None
    }
}

impl Elab {
    /// E0371 for a refinement inside an instance's signature's type that
    /// its class's type doesn't imply, and no proof could give: it would be
    /// gained (an unrefined type where the class's is refined, or the
    /// reverse for a parameter). `at`: the parameter (`pre`) or result, its
    /// type in the instance and in the class.
    #[allow(clippy::too_many_arguments)]
    fn inside_gained(&mut self, g: &super::refine::Gained, at: &(String, String, String), pre: bool, class: &str, member: &str, span: Span, note: &str) {
        let (x, mine, theirs) = at;
        let (e, f) = (self.show_val(&g.cx, &g.expected), self.show_val(&g.cx, &g.found));
        let (msg, why, help) = if pre {
            (
                format!("`{member}` requires more of `{x}` than class `{class}` does"),
                format!("a call through class `{class}` may pass any `{theirs}`, whose `{f}` values aren't known to be `{e}`"),
                format!("give `{x}` the class's type `{theirs}`, or a type it implies, and check its values in the body"),
            )
        } else {
            (
                format!("`{member}`'s result `{x}` doesn't promise what class `{class}`'s does"),
                format!("its `{f}` values aren't known to be `{e}`, as class `{class}` promises"),
                format!("give `{x}` the class's type `{theirs}`, or a type implying it"),
            )
        };
        self.err(
            Diagnostic::error("E0371", msg, span)
                .with_label(format!("`{mine}` here, `{theirs}` in the class"))
                .with_note(note.to_string())
                .with_note(format!("{why}: a refinement inside a type is never gained from an existing value"))
                .with_help(help),
        );
    }
}

/// A class's function's binders, for a check at a refinement alias (#226):
/// its class, which binder is its dictionary, which of the class's types
/// each binder is (if one), and their number.
pub(super) struct MethodLayout {
    pub class: TyId,
    pub dict: usize,
    pos: Vec<Option<usize>>,
    pub arity: usize,
}

impl Elab {
    pub(super) fn method_layout(&self, f: DefId) -> Option<MethodLayout> {
        // Its dictionary is the binder its body reads the function from
        // (`$d.make …`): a clause of the function's own (`Seq s`) may be
        // bound before it, as when the class's type is a parameter.
        let own = self.method_dict(f)?;
        let mut ty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[f.0 as usize].ty);
        let mut pos = Vec::new();
        let mut dict = None;
        let mut i = 0;
        while let Val::Pi(_, _, _, d, c) = self.force(&ty) {
            pos.push(None);
            if dict.is_none() && i == own {
                if let Val::TyCon(class, tys) = self.force(&d) {
                    if self.class_defs.contains_key(&class) {
                        dict = Some((i, class));
                        for (k, t) in tys.iter().enumerate() {
                            if let Val::Neutral(Head::Var(l), sp) = force_meta(&self.g, t.clone()) {
                                if sp.is_empty() && l < i {
                                    pos[l] = Some(k);
                                }
                            }
                        }
                    }
                }
            }
            ty = apply_closure(&self.g, &c, Val::var(i));
            i += 1;
        }
        let (dict, class) = dict?;
        Some(MethodLayout { class, dict, pos, arity: i })
    }

    /// Which binder of class function `f` is its class's dictionary: the
    /// one its body (`$d.f x …`, under a lambda per binder) reads.
    fn method_dict(&self, f: DefId) -> Option<usize> {
        let mut b = self.g.defs[f.0 as usize].body.as_ref()?;
        let mut n = 0;
        while let Tm::Lam(_, _, _, body) = b {
            b = body;
            n += 1;
        }
        match b.head() {
            Tm::Field(d, _, _) => match **d {
                Tm::Var(k) if k < n => Some(n - 1 - k),
                _ => None,
            },
            _ => None,
        }
    }

    /// `t` without the refinement aliases at its head: the type the alias
    /// stands for (`Int` for `Small`, through `Nat`).
    fn alias_base(&self, t: &Val) -> Val {
        let mut v = force_meta(&self.g, t.clone());
        for _ in 0..64 {
            if self.refined_alias(&v).is_none() {
                break;
            }
            match unfold(&self.g, &v) {
                Some(u) => v = force_meta(&self.g, u),
                None => break,
            }
        }
        v
    }

    /// Whether `t` has a refinement alias where `b`, the same type at the
    /// alias's base, doesn't, at a place a value is produced (`co`) or
    /// consumed: a type of a value given to the caller is produced where
    /// it is covariant.
    fn alias_differs(&self, lvl: usize, t: &Val, b: &Val, co: bool, depth: usize) -> bool {
        if depth > 16 {
            return false;
        }
        let (pt, pb) = (self.peel(t), self.peel(b));
        if co {
            if let Some((d, _)) = self.refined_alias(&pt) {
                if self.refined_alias(&pb).is_none_or(|(e, _)| e != d) {
                    return true;
                }
            }
        }
        match (self.force(&pt), self.force(&pb)) {
            (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 && a1.len() == a2.len() => {
                let vs = self.variance(t1);
                a1.iter().zip(a2.iter()).enumerate().any(|(k, (x, y))| match vs.get(k) {
                    Some(super::refine::Variance::Co) => self.alias_differs(lvl, x, y, co, depth + 1),
                    Some(super::refine::Variance::Contra) => self.alias_differs(lvl, x, y, !co, depth + 1),
                    _ => self.alias_differs(lvl, x, y, co, depth + 1) || self.alias_differs(lvl, x, y, !co, depth + 1),
                })
            }
            (Val::TupleTy(x), Val::TupleTy(y)) if x.len() == y.len() => x.iter().zip(y.iter()).any(|(x, y)| self.alias_differs(lvl, x, y, co, depth + 1)),
            (Val::Pi(_, _, _, a1, c1), Val::Pi(_, _, _, a2, c2)) => {
                self.alias_differs(lvl, &a1, &a2, !co, depth + 1)
                    || self.alias_differs(lvl + 1, &apply_closure(&self.g, &c1, Val::var(lvl)), &apply_closure(&self.g, &c2, Val::var(lvl)), co, depth + 1)
            }
            _ => false,
        }
    }

    /// The conditions for value `v` (a term at `env`'s level) of type `t`
    /// to be of it where `b`, the same type at the alias's base, isn't. A
    /// part a finite walk reaches gives goals about the value (under
    /// `match`es reaching it, other cases trivially true); one under a
    /// recursive type, or a function, is an `AliasGoal::Part`, checked by
    /// the instance's own type for it (`ti`, the instance's type for `v`
    /// where known) or, for a list, by `list.all`. `Err(t)` where the walk
    /// came back to the type `t` it is inside, which makes that a part.
    #[allow(clippy::too_many_arguments)]
    fn alias_goals(&self, env: &[Val], outer: usize, v: &Tm, t: &Val, b: &Val, ti: Option<&Val>, seen: &mut Vec<TyId>) -> Result<Vec<AliasGoal>, TyId> {
        let lvl = env.len();
        if !self.alias_differs(lvl, t, b, true, 0) {
            return Ok(Vec::new());
        }
        let (pt, pb) = (self.peel(t), self.peel(b));
        if let Some((d, args)) = self.refined_alias(&pt) {
            if self.refined_alias(&pb).is_none_or(|(e, _)| e != d) {
                let vv = eval(&self.g, &Rc::new(env.to_vec()), v);
                let preds = self.alias_preds.get(&d).cloned().unwrap_or_default();
                // The predicates at this use's arguments where they are
                // closed values: `n < 7` for `Below 7`, not `n < k`.
                let closed = args.iter().all(|a| !mentions_from(&quote(&self.g, lvl, a), lvl));
                let names = if closed { self.alias_param_names(&Cx::default(), d, &args) } else { Vec::new() };
                return Ok(preds
                    .iter()
                    .map(|p| {
                        let mut e = args.clone();
                        e.push(vv.clone());
                        AliasGoal::Value(quote(&self.g, lvl, &self.inst_pred(p, e)), rename_words(&p.text, &names), d)
                    })
                    .collect());
            }
        }
        let part = |seen: &mut Vec<TyId>| self.alias_part(env, outer, v, t, b, ti, seen);
        let ti = ti.map(|x| self.force(&self.peel(x)));
        let tru = quote(&self.g, lvl, &self.g.bool_val(true));
        match (self.force(&pt), self.force(&pb)) {
            (Val::TupleTy(x), Val::TupleTy(y)) => {
                let (x, y) = (crate::core::flat_parts(&self.g, &x, true), crate::core::flat_parts(&self.g, &y, true));
                if x.len() != y.len() {
                    return Ok(vec![part(seen)]);
                }
                let z = match &ti {
                    Some(Val::TupleTy(z)) => Some(crate::core::flat_parts(&self.g, z, true)).filter(|z| z.len() == x.len()),
                    _ => None,
                };
                let mut out = Vec::new();
                for (i, (a, c)) in x.iter().zip(&y).enumerate() {
                    out.extend(self.alias_goals(env, outer, &Tm::Proj(Rc::new(v.clone()), i, false), a, c, z.as_ref().map(|z| &z[i]), seen)?);
                }
                Ok(out)
            }
            (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 && a1.len() == a2.len() => {
                if Some(t1) == self.g.well_known.list {
                    return Ok(vec![part(seen)]);
                }
                if seen.contains(&t1) {
                    return Err(t1);
                }
                if seen.len() > 4 {
                    return Ok(vec![part(seen)]);
                }
                let ai = match &ti {
                    Some(Val::TyCon(t3, a3)) if *t3 == t1 && a3.len() == a1.len() => Some(a3.clone()),
                    _ => None,
                };
                seen.push(t1);
                let mut out = Vec::new();
                let mut recursive = false;
                'ctors: for c in self.g.tys[t1.0 as usize].ctors.clone() {
                    let fields = self.g.cons[c.0 as usize].fields.clone();
                    let n = fields.len();
                    let mut et = a1.to_vec();
                    let mut eb = a2.to_vec();
                    let mut ei = ai.as_deref().map(<[Val]>::to_vec);
                    let mut inner = env.to_vec();
                    let mut parts = Vec::new();
                    for (i, (_, _, _, fty)) in fields.iter().enumerate() {
                        let ft = eval(&self.g, &Rc::new(et.clone()), fty);
                        let fb = eval(&self.g, &Rc::new(eb.clone()), fty);
                        let fi = ei.as_ref().map(|e| eval(&self.g, &Rc::new(e.clone()), fty));
                        let x = Val::var(lvl + i);
                        et.push(x.clone());
                        eb.push(x.clone());
                        if let Some(e) = &mut ei {
                            e.push(x.clone());
                        }
                        parts.push((ft, fb, fi));
                        inner.push(x);
                    }
                    for (i, (ft, fb, fi)) in parts.iter().enumerate() {
                        let fv = Tm::Var(n - 1 - i);
                        let goals = match self.alias_goals(&inner, outer, &fv, ft, fb, fi.as_ref(), seen) {
                            Ok(goals) => goals,
                            Err(r) if r == t1 => {
                                recursive = true;
                                break 'ctors;
                            }
                            Err(r) => {
                                seen.pop();
                                return Err(r);
                            }
                        };
                        let case = |g: Tm| {
                            Tm::Case(Rc::new(v.clone()), Rc::new(CaseTm { branches: vec![(c, n, g)], lits: Vec::new(), default: Some(tru.clone()) }))
                        };
                        for g in goals {
                            out.push(match g {
                                AliasGoal::Value(g, text, d) => AliasGoal::Value(case(g), text, d),
                                AliasGoal::Part { t, b, inst, each, .. } => {
                                    let each = each.map(|(gs, text)| (gs.into_iter().map(case).collect(), text));
                                    AliasGoal::Part { t, b, inst, each, inside: true }
                                }
                            });
                        }
                    }
                }
                seen.pop();
                if recursive {
                    return Ok(vec![part(seen)]);
                }
                Ok(out)
            }
            _ => Ok(vec![part(seen)]),
        }
    }

    /// `alias_goals` for a call's result (`known_result_obligations`): its
    /// goals about values a finite walk reaches, each with whether it is
    /// about a value inside the result. `None` where a part isn't reached
    /// so (under a recursive type, or a function).
    #[allow(clippy::type_complexity)]
    pub(super) fn alias_goals_pub(&self, env: &[Val], v: &Tm, t: &Val, b: &Val) -> Option<Vec<(Tm, String, DefId, bool)>> {
        let goals = self.alias_goals(env, env.len(), v, t, b, None, &mut Vec::new()).ok()?;
        let inside = !self.alias_at_top(t, b);
        goals
            .into_iter()
            .map(|g| match g {
                AliasGoal::Value(g, text, d) => Some((g, text, d, inside)),
                AliasGoal::Part { .. } => None,
            })
            .collect()
    }

    /// Whether `t`, unlike `b`, has a refinement alias at its top: the
    /// goals `alias_goals` gives are then about the value itself, else
    /// about values inside it.
    fn alias_at_top(&self, t: &Val, b: &Val) -> bool {
        let (pt, pb) = (self.peel(t), self.peel(b));
        self.refined_alias(&pt).is_some_and(|(d, _)| self.refined_alias(&pb).is_none_or(|(e, _)| e != d))
    }

    /// `v` of type `t` (`b` at the alias's base) as a part `alias_goals`
    /// doesn't walk into: the instance's own type `ti` for it, if it and
    /// `t` say nothing of the values the walk bound; for a list, the goal
    /// that `list.all` elements satisfy what an element needs.
    #[allow(clippy::too_many_arguments)]
    fn alias_part(&self, env: &[Val], outer: usize, v: &Tm, t: &Val, b: &Val, ti: Option<&Val>, seen: &mut Vec<TyId>) -> AliasGoal {
        let lvl = env.len();
        let (t_full, b_full) = (t, b);
        let closed = |x: &Val| !mentions_from(&quote(&self.g, lvl, x), lvl - outer);
        let (t, b) = if closed(t) && closed(b) { (Some(t.clone()), Some(b.clone())) } else { (None, None) };
        let inst = ti.filter(|x| t.is_some() && closed(x)).cloned();
        AliasGoal::Part { each: self.list_all_goal(env, outer, v, t_full, b_full, seen), t, b, inst, inside: lvl > outer || matches!(v, Tm::Proj(..)) }
    }

    /// For `v`, a list of type `t`: the goal `list.all (\x -> g) v`, with
    /// `g` what each element needs, and how it is written. None where
    /// `t` isn't a list, `std.list` isn't loaded, or an element's goals
    /// can't be written so.
    fn list_all_goal(&self, env: &[Val], outer: usize, v: &Tm, t: &Val, b: &Val, seen: &mut Vec<TyId>) -> Option<(Vec<Tm>, String)> {
        let list = self.g.well_known.list?;
        let (Val::TyCon(l1, a1), Val::TyCon(l2, a2)) = (self.force(&self.peel(t)), self.force(&self.peel(b))) else { return None };
        if l1 != list || l2 != list || a1.len() != 1 || a2.len() != 1 {
            return None;
        }
        let all = self.g.defs.iter().position(|d| &*d.module == "std.list" && &*d.name == "all").map(|i| DefId(i as u32))?;
        let lvl = env.len();
        let mut inner = env.to_vec();
        inner.push(Val::var(lvl));
        // What each element needs, as one predicate of it.
        let mut body: Option<Tm> = None;
        let mut texts: Vec<String> = Vec::new();
        let mut subject: Option<Name> = None;
        let mut direct = true;
        for g in self.alias_goals(&inner, outer, &Tm::Var(0), &a1[0], &a2[0], None, seen).ok()? {
            let (gs, text) = match g {
                AliasGoal::Value(g, text, d) => {
                    let s = self.alias_subject.get(&d).cloned();
                    direct &= !matches!(g, Tm::Case(..) | Tm::Proj(..)) && s.is_some() && (subject.is_none() || subject == s);
                    subject = subject.or(s);
                    (vec![g], text)
                }
                AliasGoal::Part { each: Some((gs, text)), .. } if !text.is_empty() => {
                    direct &= subject.is_none();
                    texts.push(format!("{text} x"));
                    subject = Some(Rc::from("x"));
                    (gs, String::new())
                }
                _ => return None,
            };
            if !text.is_empty() {
                texts.push(text);
            }
            for g in gs {
                body = Some(match body {
                    None => g,
                    Some(a) => self.if_tm(a, g, self.bool_lit(false)),
                });
            }
        }
        let body = body?;
        let x: Name = subject.clone().unwrap_or_else(|| Rc::from("x"));
        let text = if direct { format!("list.all (\\{x} -> {})", texts.join(" and ")) } else { String::new() };
        // `list.all` at the element type at the base, the predicate, `v`.
        let mut ty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[all.0 as usize].ty);
        let mut call = Tm::Def(all);
        let mut expl = vec![Tm::Lam(x, Mult::Many, Icit::Expl, Rc::new(body)), v.clone()].into_iter();
        while let Val::Pi(_, m, icit, _, c) = self.force(&ty) {
            let (a, va) = match icit {
                Icit::Impl => (quote(&self.g, lvl, &a2[0]), a2[0].clone()),
                Icit::Expl => (expl.next()?, Val::var(usize::MAX / 2)),
            };
            call = Tm::App(Rc::new(call), Rc::new(a), icit, m);
            ty = apply_closure(&self.g, &c, va);
        }
        if expl.next().is_some() {
            return None;
        }
        Some((vec![call], text))
    }

    /// The obligations of one class's function `f` used at a refinement
    /// alias through dictionary `ad` (#226): at the call `call` (its
    /// facts known), or, without one, at any arguments its signature
    /// allows at the alias (where generic code may call it). The values of
    /// the class's type it gives are of the alias; a function it is given
    /// is called only with values of the alias.
    fn alias_method_obligations(&mut self, ad: &AliasDict, f: DefId, call: Option<(&Cx, &Tm, Span)>) {
        let Some(lay) = self.method_layout(f) else { return };
        let member = self.g.defs[f.0 as usize].name.rsplit('.').next().unwrap_or_default().to_string();
        let cname = self.class_defs.get(&ad.class).map(|c| c.name.clone()).unwrap_or_default();
        let alias_ty = &ad.tys[ad.pos];
        let base_ty = self.alias_base(alias_ty);
        let mut cx = match call {
            Some((cx, _, _)) => cx.clone(),
            None => (*ad.cx).clone(),
        };
        let alias_s = self.show_val(&cx, alias_ty);
        let base_s = self.show_val(&cx, &base_ty);
        let span = call.map_or(ad.span, |c| c.2);
        let fty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[f.0 as usize].ty);
        // The arguments: the call's, or the class's types, the dictionary
        // and a local for each other binder.
        let call_args: Option<Vec<(Val, Icit, Mult)>> = call.map(|(cx, t, _)| {
            let mut rev = Vec::new();
            let mut h: &Tm = t;
            while let Tm::App(g, a, i, m) = h {
                rev.push((self.eval(cx, a), *i, *m));
                h = g;
            }
            rev.reverse();
            rev
        });
        let dict_v = self.eval(&cx, &ad.dict);
        let mut ty_t = fty.clone();
        let mut ty_b = fty;
        let mut args_t: Vec<(Val, Icit, Mult)> = Vec::new();
        let mut params: Vec<(usize, String, Val, Val)> = Vec::new();
        for i in 0..lay.arity {
            let (Val::Pi(x, m, icit, dt, ct), Val::Pi(_, _, _, db, cb)) = (self.force(&ty_t), self.force(&ty_b)) else { return };
            let (vt, vb) = match (&call_args, lay.pos[i]) {
                (Some(a), _) => {
                    let Some((v, _, _)) = a.get(i) else { return };
                    match lay.pos[i] {
                        Some(k) if k == ad.pos => (v.clone(), base_ty.clone()),
                        _ => (v.clone(), v.clone()),
                    }
                }
                (None, Some(k)) => {
                    let v = ad.tys[k].clone();
                    if k == ad.pos { (v, base_ty.clone()) } else { (v.clone(), v) }
                }
                (None, None) if i == lay.dict => (dict_v.clone(), dict_v.clone()),
                (None, None) => {
                    let l = cx.bind(&x, (*dt).clone(), m);
                    (Val::var(l), Val::var(l))
                }
            };
            if icit == Icit::Expl && lay.pos[i].is_none() {
                params.push((i, x.to_string(), (*dt).clone(), (*db).clone()));
            }
            args_t.push((vt.clone(), icit, m));
            ty_t = apply_closure(&self.g, &ct, vt);
            ty_b = apply_closure(&self.g, &cb, vb);
        }
        let lvl = cx.lvl();
        let mut value = Tm::Def(f);
        for (a, i, m) in &args_t {
            value = Tm::App(Rc::new(value), Rc::new(quote(&self.g, lvl, a)), *i, *m);
        }
        // Without a call: the class's preconditions hold of the arguments.
        if call.is_none() {
            if let Some(spec) = self.specs.get(&f).cloned() {
                let mut env: Vec<Val> = args_t.iter().map(|a| a.0.clone()).collect();
                env.truncate(spec.n_binders);
                env.push(self.eval(&cx, &value));
                for p in spec.preds.iter().filter(|p| !p.is_post) {
                    let v = self.inst_pred(p, env.clone());
                    cx.assume(v);
                }
            }
        }
        let call_text = call.map(|(_, _, s)| self.src_text(s));
        // The instance that runs: the class at its types, the alias's base
        // in the alias's place (`Conv Bool Int`).
        let inst_s = std::iter::once(cname.clone())
            .chain(ad.tys.iter().enumerate().map(|(k, t)| {
                let t = if k == ad.pos { base_ty.clone() } else { t.clone() };
                let s = self.show_val(&cx, &t);
                if s.contains(' ') && !(s.starts_with('(') && s.ends_with(')')) { format!("({s})") } else { s }
            }))
            .collect::<Vec<_>>()
            .join(" ");
        let kind = |param: Option<super::AliasParam>, inside: bool, whole: Option<(String, String)>| ObKind::AtAlias {
            inst: inst_s.clone(),
            class: cname.clone(),
            alias: alias_s.clone(),
            base: base_s.clone(),
            member: member.clone(),
            call: call_text.clone(),
            param,
            inside,
            whole,
        };
        let falsity = quote(&self.g, lvl, &self.g.bool_val(false));
        let saved = self.cur_fn;
        self.cur_fn = ad.owner;
        // The instance's own types for its parameters and result, from its
        // signature, at these arguments.
        let (inst_params, inst_result) = self.inst_param_types(ad.members.get(&member).copied(), &args_t);
        // Its result.
        let env = cx.env.to_vec();
        let top = self.alias_at_top(&ty_t, &ty_b);
        let goals = match self.alias_goals(&env, lvl, &value, &ty_t, &ty_b, inst_result.as_ref(), &mut Vec::new()) {
            Ok(goals) => goals,
            Err(_) => vec![AliasGoal::Part { t: None, b: None, inst: None, each: None, inside: false }],
        };
        for goal in goals {
            match goal {
                AliasGoal::Value(g, text, d) => {
                    // The result itself is shown as the call; a value inside
                    // it (a tuple's part, `Some`'s) by the alias's own name.
                    let inside = !top;
                    let text = match (&call_text, inside) {
                        (Some(c), false) => {
                            let subject = self.alias_subject.get(&d).map(|s| s.to_string()).unwrap_or_default();
                            rename_words(&text, &[(subject, if c.contains(' ') { format!("({c})") } else { c.clone() })])
                        }
                        _ => text,
                    };
                    let goal = self.eval(&cx, &g);
                    self.oblige(&cx, span, kind(None, inside, None), text, goal, None);
                }
                AliasGoal::Part { t, b, inst, each, inside } => {
                    let whole = t.as_ref().zip(b.as_ref()).map(|(t, b)| (self.show_val(&cx, t), self.show_val(&cx, b)));
                    // The instance's signature gives it a type that implies
                    // the class's at the alias (D85): `List Nat`, `Tree Small`,
                    // `(x~Int -> y~Int, y >= 0)` for `Int -> Nat`.
                    if let (Some(t), Some(i)) = (&t, &inst) {
                        let n = self.obligations.len();
                        if self.refined_implies(&cx, t, i, span, kind(None, inside, whole.clone())) {
                            continue;
                        }
                        self.obligations.truncate(n);
                    }
                    // A list: `list.all` of its elements, from what the
                    // prover knows of it (the instance's postconditions).
                    if let Some((gs, text)) = each {
                        for g in gs {
                            let goal = self.eval(&cx, &g);
                            self.oblige(&cx, span, kind(None, inside, whole.clone()), text.clone(), goal, None);
                        }
                        continue;
                    }
                    let goal = self.eval(&cx, &falsity);
                    self.oblige(&cx, span, kind(None, inside, whole), String::new(), goal, None);
                }
            }
        }
        // Its function parameters: the instance calls them with values it
        // gives, and hands them functions giving such values. The class's
        // type for each at the alias must imply the instance's own (its
        // signature's, #225, else the class's at the base), as a refined
        // function type does (D85): at any depth, refinements written as
        // aliases or inline.
        for (i, x, dt, db) in params {
            if !self.alias_differs(lvl, &dt, &db, false, 0) {
                continue;
            }
            let param = Some(self.alias_param(&cx, &x, &dt, &db, &alias_s));
            let idom = inst_params.get(&i).cloned().unwrap_or(db);
            if !self.refined_implies(&cx, &idom, &dt, span, kind(param.clone(), false, None)) {
                let goal = self.eval(&cx, &falsity);
                self.oblige(&cx, span, kind(param, false, None), format!("every value it gives `{x}` is a `{alias_s}`"), goal, None);
            }
        }
        self.cur_fn = saved;
    }

    /// The places in `t` where it has a refinement alias that `b`, the same
    /// type at the alias's base, doesn't, at which a value is produced
    /// (`co`), as `alias_differs` finds them: each as the steps reaching it.
    fn alias_paths(&self, lvl: usize, t: &Val, b: &Val, co: bool, path: &mut Vec<Step>, out: &mut Vec<Vec<Step>>) {
        if path.len() > 16 || out.len() > 4 {
            return;
        }
        let (pt, pb) = (self.peel(t), self.peel(b));
        if co {
            if let Some((d, _)) = self.refined_alias(&pt) {
                if self.refined_alias(&pb).is_none_or(|(e, _)| e != d) {
                    out.push(path.clone());
                    return;
                }
            }
        }
        let mut at = |s: &Elab, step: Step, x: &Val, y: &Val, co: bool, lvl: usize, out: &mut Vec<Vec<Step>>| {
            path.push(step);
            s.alias_paths(lvl, x, y, co, path, out);
            path.pop();
        };
        match (self.force(&pt), self.force(&pb)) {
            (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 && a1.len() == a2.len() => {
                let vs = self.variance(t1);
                for (k, (x, y)) in a1.iter().zip(a2.iter()).enumerate() {
                    match vs.get(k) {
                        Some(super::refine::Variance::Co) => at(self, Step::Part, x, y, co, lvl, out),
                        Some(super::refine::Variance::Contra) => at(self, Step::Other, x, y, !co, lvl, out),
                        _ => {
                            at(self, Step::Other, x, y, co, lvl, out);
                            at(self, Step::Other, x, y, !co, lvl, out);
                        }
                    }
                }
            }
            (Val::TupleTy(x), Val::TupleTy(y)) if x.len() == y.len() => {
                for (x, y) in x.iter().zip(y.iter()) {
                    at(self, Step::Part, x, y, co, lvl, out);
                }
            }
            (Val::Pi(_, _, _, a1, c1), Val::Pi(_, _, _, a2, c2)) => {
                at(self, Step::Arg, &a1, &a2, !co, lvl, out);
                let (r1, r2) = (apply_closure(&self.g, &c1, Val::var(lvl)), apply_closure(&self.g, &c2, Val::var(lvl)));
                at(self, Step::Res, &r1, &r2, co, lvl + 1, out);
            }
            _ => {}
        }
    }

    /// Function parameter `x` of type `t` at the alias (`b` at its base),
    /// as a message about the values of the alias the instance gives it
    /// says it (#254): where it gives them (its argument, a function's
    /// results, …), from the places `t` has the alias.
    fn alias_param(&self, cx: &Cx, x: &str, t: &Val, b: &Val, alias: &str) -> super::AliasParam {
        let lvl = cx.lvl();
        let mut paths = Vec::new();
        self.alias_paths(lvl, t, b, false, &mut Vec::new(), &mut paths);
        let a = format!("`{alias}`");
        let mut gives: Vec<String> = Vec::new();
        let mut only: Vec<String> = Vec::new();
        for p in &paths {
            // A function of several arguments gives its results after the
            // last: `Int -> Int -> t` is a function whose results are `t`s.
            let mut p = p.clone();
            p.dedup_by(|x, y| *x == Step::Res && *y == Step::Res);
            let (g, o) = match p.split_first() {
                Some((Step::Arg, rest)) => (given_one(rest, &a), given_all(rest, &a, false)),
                _ => (None, None),
            };
            let g = g.unwrap_or_else(|| format!("a value that isn't a {a}"));
            let o = o.unwrap_or_else(|| format!("{a}s"));
            if !gives.contains(&g) {
                gives.push(g);
            }
            if !only.contains(&o) {
                only.push(o);
            }
        }
        if gives.is_empty() {
            gives.push(format!("a value that isn't a {a}"));
            only.push(format!("{a}s"));
        }
        let direct = paths.iter().all(|p| p.as_slice() == [Step::Arg]);
        let (bt, tt) = (self.peel(b), self.peel(t));
        let accepts = match self.force(&bt) {
            Val::Pi(_, _, _, d, _) => self.show_val(cx, &d),
            _ => self.show_val(cx, &bt),
        };
        let example = (!direct).then(|| {
            let s = self.show_val(cx, &tt);
            if s.contains(' ') { format!("({s})") } else { s }
        });
        super::AliasParam { name: x.to_string(), gives: gives.join(" or "), only: only.join(" and "), accepts, example }
    }

    /// The types an instance's function `g` gives its explicit parameters,
    /// by the class's binder each is (its explicit ones, in order), and its
    /// result, at the class's arguments `args`: where `g`'s signature says
    /// them in terms of `args` alone. None where the two don't line up.
    fn inst_param_types(&self, g: Option<DefId>, args: &[(Val, Icit, Mult)]) -> (HashMap<usize, Val>, Option<Val>) {
        let mut out = HashMap::new();
        let Some(g) = g else { return (out, None) };
        let class_expl: Vec<usize> = (0..args.len()).filter(|i| args[*i].1 == Icit::Expl).collect();
        let mut ty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[g.0 as usize].ty);
        let (mut j, mut k) = (0, 0);
        let mut found = Vec::new();
        while let Val::Pi(_, _, icit, d, c) = self.force(&ty) {
            // Its own implicit binders (an instance's type variables) are
            // placeholders no context binds.
            let v = match icit {
                Icit::Expl => {
                    let Some(i) = class_expl.get(j) else { return (out, None) };
                    found.push((*i, (*d).clone()));
                    j += 1;
                    args[*i].0.clone()
                }
                _ => Val::var(PLACEHOLDER + k),
            };
            ty = apply_closure(&self.g, &c, v);
            k += 1;
        }
        if j != class_expl.len() {
            return (out, None);
        }
        for (i, d) in found {
            if !mentions_placeholder(&self.g, &d) {
                out.insert(i, d);
            }
        }
        (out, Some(ty).filter(|t| !mentions_placeholder(&self.g, t)))
    }

    /// The dictionaries found through a refinement alias in this module
    /// (#226): at a call of a class's function, that call's obligations;
    /// otherwise (passed to generic code, or an instance's context) every
    /// function of the class's, at any arguments.
    pub(super) fn alias_dict_obligations(&mut self) {
        let dicts = std::mem::take(&mut self.alias_dicts);
        let calls = std::mem::take(&mut self.class_calls);
        let uses = std::mem::take(&mut self.class_value_uses);
        let local_calls = std::mem::take(&mut self.class_local_calls);
        if dicts.is_empty() {
            return;
        }
        // The calls whose dictionary is a request's: one, or each call of
        // a local defined as the class's function (#252).
        let mut direct: HashMap<MetaId, Vec<(DefId, PendingPre)>> = HashMap::new();
        let calls = calls.into_iter().filter_map(|c| match c.call.spine() {
            (Tm::Def(f), spine) => {
                let lay = self.method_layout(*f)?;
                match spine.get(lay.dict).map(|d| d.head()) {
                    Some(Tm::Meta(m)) if spine.len() >= lay.arity => Some((*m, c)),
                    _ => None,
                }
            }
            _ => None,
        });
        for (m, c) in calls.collect::<Vec<_>>().into_iter().chain(local_calls) {
            if let Tm::Def(f) = c.call.head() {
                direct.entry(m).or_default().push((*f, c));
            }
        }
        // Its uses as a value: those not compared with an expected type
        // are checked at any arguments, where they are.
        let mut values: HashMap<MetaId, Vec<(DefId, Span)>> = HashMap::new();
        for (m, f, span, _) in &uses {
            let at = values.entry(*m).or_default();
            if !uses.iter().any(|(n, _, s, checked)| n == m && s == span && *checked) && !at.contains(&(*f, *span)) {
                at.push((*f, *span));
            }
        }
        let mut done = HashSet::new();
        let saved_spec = self.in_spec;
        self.in_spec = 0;
        for ad in dicts {
            let key = (ad.span, ad.class, ad.pos, format!("{:?}", ad.dict), ad.meta);
            if !done.insert(key) {
                continue;
            }
            // Each call, and each use as a value (#252).
            let cs = ad.meta.and_then(|m| direct.get(&m));
            let used = ad.meta.is_some_and(|m| uses.iter().any(|u| u.0 == m));
            if cs.is_some() || used {
                for (f, c) in cs.into_iter().flatten() {
                    let (f, cx) = (*f, c.cx.clone());
                    let call = crate::core::zonk_metas(&self.g, cx.lvl(), &c.call);
                    self.alias_method_obligations(&ad, f, Some((&cx, &call, c.span)));
                }
                for (f, span) in ad.meta.and_then(|m| values.get(&m)).into_iter().flatten() {
                    let at = AliasDict { span: *span, ..ad.clone() };
                    self.alias_method_obligations(&at, *f, None);
                }
                continue;
            }
            let mut fs: Vec<DefId> =
                self.class_methods.iter().copied().filter(|f| self.method_layout(*f).is_some_and(|l| l.class == ad.class)).collect();
            fs.sort();
            for f in fs {
                self.alias_method_obligations(&ad, f, None);
            }
        }
        self.in_spec = saved_spec;
    }
}

/// One condition for a value of a type with a refinement alias inside to be
/// of it, where the same type at the alias's base isn't (`alias_goals`).
enum AliasGoal {
    /// A goal about the value (under `match`es reaching the part), the
    /// predicate as written, and the alias.
    Value(Tm, String, DefId),
    /// A part a finite walk doesn't reach (a recursive type, a function),
    /// inside the value or the value itself: its type at the alias and at
    /// the base (if they say nothing of values the walk bound), the
    /// instance's own type for it (likewise), and for a list, the goals
    /// that `list.all` its elements are of the alias, and how written.
    Part { t: Option<Val>, b: Option<Val>, inst: Option<Val>, each: Option<(Vec<Tm>, String)>, inside: bool },
}

/// Whether `t` mentions one of the `n` innermost variables it is under.
fn mentions_from(t: &Tm, n: usize) -> bool {
    fn go(t: &Tm, depth: usize, n: usize) -> bool {
        match t {
            Tm::Var(i) => *i >= depth && *i < depth + n,
            _ => t.any_sub(|x, k| go(x, depth + k, n)),
        }
    }
    go(t, 0, n)
}

/// The first level of the placeholders standing for an instance function's
/// own binders, which no context binds.
const PLACEHOLDER: usize = usize::MAX / 4;

/// Whether `v` mentions a placeholder (`PLACEHOLDER` and above). Quoted
/// above every level, so that none underflows.
fn mentions_placeholder(g: &Globals, v: &Val) -> bool {
    const TOP: usize = usize::MAX / 2;
    fn go(t: &Tm, depth: usize) -> bool {
        match t {
            Tm::Var(i) if *i >= depth => TOP - 1 - (i - depth) >= PLACEHOLDER,
            _ => t.any_sub(|x, n| go(x, depth + n)),
        }
    }
    go(&quote(g, TOP, v), 0)
}

/// A step into a type, to a place a refinement alias is (#254): a
/// function's argument or result, a part of a value (a covariant type
/// argument, a tuple's component), or anything else.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Step {
    Arg,
    Res,
    Part,
    Other,
}

/// What a value given at `path` is, one of them, where it isn't of alias
/// `a` (`a function whose results aren't `Nat`s`). None for a place this
/// can't say.
fn given_one(path: &[Step], a: &str) -> Option<String> {
    match path {
        [] => Some(format!("a value that isn't a {a}")),
        [Step::Res, rest @ ..] => Some(format!("a function whose results {}", given_pred(rest, a, true)?)),
        [Step::Part, rest @ ..] => Some(format!("a value with parts that {}", given_pred(rest, a, true)?)),
        [Step::Arg, Step::Arg, rest @ ..] => Some(format!("a function that calls its function argument with {}", given_all(rest, a, true)?)),
        _ => None,
    }
}

/// The values given at `path`, all of them: those that aren't of alias `a`
/// (`neg`), or those that are.
fn given_all(path: &[Step], a: &str, neg: bool) -> Option<String> {
    match path {
        [] if neg => Some(format!("values that aren't {a}s")),
        [] => Some(format!("{a}s")),
        [Step::Res, rest @ ..] => Some(format!("functions whose results {}", given_pred(rest, a, neg)?)),
        [Step::Part, rest @ ..] => Some(format!("values with parts that {}", given_pred(rest, a, neg)?)),
        [Step::Arg, Step::Arg, rest @ ..] => Some(format!("functions that call their function arguments with {}", given_all(rest, a, neg)?)),
        _ => None,
    }
}

/// What the values at `path` are, said of several: `aren't `Nat`s`, `are
/// functions whose results …`.
fn given_pred(path: &[Step], a: &str, neg: bool) -> Option<String> {
    match path {
        [] if neg => Some(format!("aren't {a}s")),
        [] => Some(format!("are {a}s")),
        [Step::Part, rest @ ..] => Some(format!("have parts that {}", given_pred(rest, a, neg)?)),
        _ => Some(format!("are {}", given_all(path, a, neg)?)),
    }
}
