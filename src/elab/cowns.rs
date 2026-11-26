//! Distinct cowns (§8.5, §7.1): a `when` naming two or more cowns has the
//! obligation that they differ, and a call tells the prover which cowns
//! it returns are new.
//!
//! A call can return only cowns it made and cowns it can reach: there are
//! no globals, and making a cown needs a `Sched`. So each cown in the value
//! of a call with effects (`effects.rs`), of a type no argument can hold,
//! differs from every cown of that type in scope.

use super::*;

/// A cown in a value, or a list of cowns: the value and the cown's
/// content type.
enum Held {
    Cown(Val, Val),
    List(Val, Val),
}

/// A cown a `when` names: its binder, the cown as written, whether it is a
/// parameter of the function, its value and its content type.
pub(super) struct HeldCown {
    name: String,
    text: String,
    span: Span,
    param: bool,
    val: Val,
    ty: Val,
}

/// A `when` naming two or more cowns, whose obligations wait until the
/// types are known: where it is, and its cowns.
pub struct PendingDistinct {
    cx: Cx,
    owner: Option<DefId>,
    span: Span,
    held: Vec<HeldCown>,
}

impl Elab {
    /// Whether types `a` and `b` differ for every instantiation of the type
    /// variables and unknowns in them.
    pub(super) fn types_apart(&self, a: &Val, b: &Val) -> bool {
        match (self.force(a), self.force(b)) {
            (Val::TyCon(i, xs), Val::TyCon(j, ys)) => i != j || xs.iter().zip(ys.iter()).any(|(x, y)| self.types_apart(x, y)),
            (Val::TupleTy(xs), Val::TupleTy(ys)) => xs.len() != ys.len() || xs.iter().zip(ys.iter()).any(|(x, y)| self.types_apart(x, y)),
            (Val::Con(c, xs), Val::Con(d, ys)) => c != d || xs.iter().zip(ys.iter()).any(|(x, y)| self.types_apart(x, y)),
            (Val::Lit(x), Val::Lit(y)) => x != y,
            (Val::Pi(..), Val::Pi(..)) => false,
            // A number literal's type, not known yet, is a number's.
            (Val::Neutral(Head::Meta(m), _), t) | (t, Val::Neutral(Head::Meta(m), _)) if self.numeric_meta(m) => match t {
                Val::TyCon(id, _) => Some(id) != self.g.well_known.int,
                Val::TupleTy(_) | Val::Pi(..) => true,
                _ => false,
            },
            (Val::TyCon(..) | Val::TupleTy(_) | Val::Pi(..), Val::TyCon(..) | Val::TupleTy(_) | Val::Pi(..)) => true,
            _ => false,
        }
    }

    /// Whether a value of type `ty` can hold a value of a type `hit`
    /// accepts: as itself, a part, a field, an element or a cown's
    /// contents. What a function, a type variable or an unknown can hold
    /// is `unknown`.
    pub(super) fn can_hold(&self, lvl: usize, ty: &Val, hit: &dyn Fn(&Elab, &Val) -> bool, unknown: bool, depth: usize, seen: &mut Vec<(TyId, Vec<Tm>)>) -> bool {
        if depth > 32 {
            return unknown;
        }
        let t = self.force(ty);
        if hit(self, &t) {
            return true;
        }
        match t {
            Val::Pi(..) | Val::Error => unknown,
            Val::TupleTy(ts) => ts.iter().any(|t| self.can_hold(lvl, t, hit, unknown, depth + 1, seen)),
            Val::TyCon(id, args) => {
                let ctors = self.g.tys[id.0 as usize].ctors.clone();
                if ctors.is_empty() {
                    // A built-in type: what its type arguments can hold.
                    return args.iter().any(|a| self.can_hold(lvl, a, hit, unknown, depth + 1, seen));
                }
                let key: Vec<Tm> = args.iter().map(|a| quote(&self.g, lvl, a)).collect();
                if seen.iter().any(|(i, k)| *i == id && k.len() == key.len() && k.iter().zip(&key).all(|(a, b)| tm_eq(a, b))) {
                    return false;
                }
                seen.push((id, key));
                let found = ctors.iter().any(|c| {
                    let fields = self.g.cons[c.0 as usize].fields.clone();
                    fields.iter().enumerate().any(|(i, f)| {
                        if f.1 == Mult::Zero {
                            return false;
                        }
                        let mut env = args.to_vec();
                        env.extend(std::iter::repeat_n(Val::Error, i));
                        let fty = eval(&self.g, &Rc::new(env), &f.3);
                        self.can_hold(lvl, &fty, hit, unknown, depth + 1, seen)
                    })
                });
                seen.pop();
                found
            }
            // An unknown that only a number can solve (a literal's type).
            Val::Neutral(Head::Meta(m), _) if self.numeric_meta(m) => false,
            Val::Neutral(..) => unknown,
            _ => false,
        }
    }

    /// Whether `a` and `b` are one type, so that cowns holding them can be
    /// compared: a number literal's type, not known yet, is `Int`'s or a
    /// refinement of it, as is any type built on `Int`.
    fn one_cown_type(&self, lvl: usize, a: &Val, b: &Val) -> bool {
        let number = |v: &Val| match self.force(v) {
            Val::Neutral(Head::Meta(m), _) => self.numeric_meta(m),
            Val::TyCon(id, _) => Some(id) == self.g.well_known.int,
            _ => false,
        };
        if number(a) && number(b) {
            return true;
        }
        let (qa, qb) = (quote(&self.g, lvl, a), quote(&self.g, lvl, b));
        !has_meta(&qa) && !has_meta(&qb) && unify(&self.g, lvl, a, b).is_ok()
    }

    /// Whether the unknown `m` is the type of a number (D38).
    fn numeric_meta(&self, m: MetaId) -> bool {
        self.deferred.iter().any(|d| d.kind == OpClass::Numeric && matches!(self.force(&d.ty), Val::Neutral(Head::Meta(m2), _) if m2 == m))
    }

    fn is_cown(&self, t: &Val) -> Option<Val> {
        match t {
            Val::TyCon(id, args) if Some(*id) == self.g.well_known.cown => args.first().cloned(),
            _ => None,
        }
    }

    /// Whether a value of type `ty` can reach a cown holding a `u`.
    fn reaches_cown(&self, lvl: usize, ty: &Val, u: &Val) -> bool {
        self.can_hold(lvl, ty, &|e: &Elab, t: &Val| e.is_cown(t).is_some_and(|w| !e.types_apart(&w, u)), true, 0, &mut Vec::new())
    }

    /// The cowns, and lists of cowns, in value `v` of type `ty`: itself, the
    /// parts of a tuple, the fields of a record. `lists`: lists of cowns too.
    fn held(&self, v: &Val, ty: &Val, lists: bool, depth: usize, out: &mut Vec<Held>) {
        if depth > 3 {
            return;
        }
        let t = self.force(ty);
        if let Some(u) = self.is_cown(&t) {
            out.push(Held::Cown(v.clone(), u));
            return;
        }
        match t {
            Val::TyCon(id, args) if lists && Some(id) == self.g.well_known.list => {
                if let Some(u) = args.first().and_then(|a| self.is_cown(&self.force(a))) {
                    out.push(Held::List(v.clone(), u));
                }
            }
            Val::TupleTy(ts) => {
                for (i, t) in ts.iter().enumerate() {
                    let p = crate::core::elim(&self.g, v.clone(), Elim::Proj(i, false));
                    self.held(&p, t, lists, depth + 1, out);
                }
            }
            Val::TyCon(id, args) => {
                let ti = &self.g.tys[id.0 as usize];
                let [c] = ti.ctors[..] else { return };
                if !ti.is_record {
                    return;
                }
                let fields = self.g.cons[c.0 as usize].fields.clone();
                let mut env = args.to_vec();
                for (i, f) in fields.iter().enumerate() {
                    let x = crate::core::elim(&self.g, v.clone(), Elim::Field(c, i));
                    if f.1 != Mult::Zero {
                        let fty = eval(&self.g, &Rc::new(env.clone()), &f.3);
                        self.held(&x, &fty, lists, depth + 1, out);
                    }
                    env.push(x);
                }
            }
            _ => {}
        }
    }

    /// A `when`'s cowns (`cowns`, holding `tys`) differ, each pair whose
    /// types don't differ for every instantiation (§8.5). Decided once the
    /// module's bodies are checked, when the types are known
    /// (`distinct_cown_obligations`).
    pub(super) fn oblige_distinct_cowns(&mut self, cx: &Cx, w: &ast::When, cowns: &[Tm], tys: &[Val]) {
        if cowns.len() < 2 || self.in_spec > 0 {
            return;
        }
        // Both the function's own parameters: the caller can be asked.
        let param = |e: &ast::Expr| match &e.kind {
            ast::ExprKind::Var(n) => cx.lookup(n).is_some_and(|l| cx.locals[l].param.is_some()),
            _ => false,
        };
        let held = w
            .binds
            .iter()
            .zip(cowns.iter().zip(tys))
            .map(|((n, e), (c, t))| HeldCown { name: n.name.clone(), text: self.expr_text(e), span: e.span, param: param(e), val: self.eval(cx, c), ty: t.clone() })
            .collect();
        let end = w.binds.last().map_or(w.span.end, |(_, e)| e.span.end);
        let span = Span { start: w.span.start, end };
        self.pending_distinct.push(PendingDistinct { cx: cx.clone(), owner: self.cur_fn, span, held });
    }

    /// The obligations of the `when`s `oblige_distinct_cowns` put off.
    pub(super) fn distinct_cown_obligations(&mut self) {
        let saved = self.cur_fn;
        for PendingDistinct { cx, owner, span, held } in std::mem::take(&mut self.pending_distinct) {
            self.cur_fn = owner;
            let func = owner.map(|d| self.g.defs[d.0 as usize].name.to_string());
            let lvl = cx.lvl();
            let shown = |t: &String| if t.contains(' ') { format!("({t})") } else { t.clone() };
            for j in 1..held.len() {
                for i in 0..j {
                    let (a, b) = (&held[i], &held[j]);
                    let (qa, qb) = (quote(&self.g, lvl, &a.ty), quote(&self.g, lvl, &b.ty));
                    if has_meta(&qa) || has_meta(&qb) || self.types_apart(&a.ty, &b.ty) {
                        continue;
                    }
                    // Types that may be equal but aren't here (`Cown a`,
                    // `Cown Nat`): `!=` can't compare the cowns, so nothing
                    // proves it.
                    let unlike = unify(&self.g, lvl, &a.ty, &b.ty).is_err();
                    let goal = if unlike { self.false_val() } else { Self::prim_val(Prim::Ne, vec![a.val.clone(), b.val.clone()]) };
                    let same = a.text == b.text;
                    let names = cx.names();
                    let cown = |q: &Tm| show(&self.g, &names, &Tm::TyConApp(self.g.well_known.cown.unwrap(), vec![q.clone()]));
                    let kind = ObKind::DistinctCowns {
                        first: a.text.clone(),
                        second: b.text.clone(),
                        held: same.then(|| a.name.clone()),
                        caller: func.clone().filter(|_| a.param && b.param),
                        unlike: unlike.then(|| (cown(&qa), cown(&qb))),
                    };
                    let text = format!("{} != {}", shown(&a.text), shown(&b.text));
                    self.oblige(&cx, if same { b.span } else { span }, kind, text, goal, None);
                }
            }
        }
        self.cur_fn = saved;
    }

    /// The facts about `v`, the value of a call with effects of type `ty`
    /// given values of types `given` (§7.1): each cown in it of a type no
    /// value given can reach differs from every cown of its type in scope.
    pub(super) fn assume_new_cowns(&mut self, cx: &mut Cx, v: &Val, ty: &Val, given: &[Val]) {
        let lvl = cx.lvl();
        let mut mine = Vec::new();
        self.held(v, ty, false, 0, &mut mine);
        let new: Vec<(Val, Val)> = mine
            .into_iter()
            .filter_map(|m| match m {
                Held::Cown(x, u) if !given.iter().any(|g| self.reaches_cown(lvl, g, &u)) => Some((x, u)),
                _ => None,
            })
            .collect();
        if new.is_empty() {
            return;
        }
        let mut scope = Vec::new();
        for k in 0..lvl {
            if matches!(self.force(&cx.locals[k].ty), Val::Univ(_) | Val::Pi(..)) {
                continue;
            }
            self.held(&cx.env[k].clone(), &cx.ty_of(k), true, 0, &mut scope);
        }
        let contains = self.g.defs.iter().position(|d| &*d.module == "std.list" && &*d.name == "contains").map(|i| DefId(i as u32));
        let mut seen: Vec<Tm> = Vec::new();
        for (x, u) in &new {
            for s in &scope {
                let fact = match s {
                    Held::Cown(k, w) if self.one_cown_type(lvl, u, w) => Self::prim_val(Prim::Ne, vec![x.clone(), k.clone()]),
                    Held::List(ks, w) if self.one_cown_type(lvl, u, w) => {
                        let Some(c) = contains else { continue };
                        let cown = self.ty_val(self.g.well_known.cown, vec![w.clone()]);
                        let f = eval(&self.g, &Rc::new(Vec::new()), &Tm::Def(c));
                        let f = crate::core::app(&self.g, f, cown, Icit::Impl);
                        let f = crate::core::app(&self.g, f, ks.clone(), Icit::Expl);
                        let f = crate::core::app(&self.g, f, x.clone(), Icit::Expl);
                        self.is_bool(f, false)
                    }
                    _ => continue,
                };
                let q = quote(&self.g, lvl, &fact);
                if !seen.iter().any(|s| tm_eq(s, &q)) {
                    seen.push(q);
                    cx.assume(fact);
                }
            }
        }
    }
}

/// Does `t` mention an unknown?
fn has_meta(t: &Tm) -> bool {
    matches!(t, Tm::Meta(_)) || t.any_sub(|s, _| has_meta(s))
}
