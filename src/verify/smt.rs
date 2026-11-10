//! Translation of an obligation to SMT-LIB 2 (SPEC §7.3).
//!
//! Every term is translated together with its sort. Sorts only depend on type
//! arguments, never on values, so a dependent family such as `Parsed a src k`
//! becomes the parametric datatype `Parsed a`. Functions defined in the module
//! (and imported `transparent` ones) are reflected as `define-fun-rec`,
//! instantiated per type; others are uninterpreted. Every application of a
//! function with a postcondition contributes that postcondition (D50).

use crate::core::{eval, force, quote, CaseTm, ConId, DefId, Lit, Mult, Prim, Tm, TyId, Val};
use crate::elab::{Elab, ObLocal, Obligation};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;
use std::rc::Rc;

/// Why an obligation can't be sent to the solver (E0451).
#[derive(Debug, Clone)]
pub struct Outside(pub String);

type Tx<T> = Result<T, Outside>;

fn out<T>(why: impl Into<String>) -> Tx<T> {
    Err(Outside(why.into()))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    Int,
    Bool,
    Str,
    Bytes,
    Bag,
    /// A datatype with its type arguments.
    Data(TyId, Vec<Sort>),
    Tuple(Vec<Sort>),
    /// An uninterpreted sort: an abstract type or a type variable.
    Unin(String, Vec<Sort>),
}

fn sym(s: &str) -> String {
    format!("|{}|", s.replace('|', "_"))
}

impl Sort {
    fn render(&self, e: &Elab) -> String {
        match self {
            Sort::Int => "Int".into(),
            Sort::Bool => "Bool".into(),
            // A string is its UTF-8 bytes (§7.3): `++`, `len` and `utf8.encode`
            // are then native, and literals are byte sequences.
            Sort::Str => "(Seq Int)".into(),
            Sort::Bytes => "(Seq Int)".into(),
            Sort::Bag => "(Array Int Int)".into(),
            Sort::Data(t, args) => apply_sort(ty_sym(e, *t), args, e),
            Sort::Tuple(args) => apply_sort(tuple_sym(args.len()), args, e),
            Sort::Unin(n, args) => apply_sort(sym(n), args, e),
        }
    }
}

fn apply_sort(head: String, args: &[Sort], e: &Elab) -> String {
    if args.is_empty() {
        head
    } else {
        format!("({head} {})", args.iter().map(|a| a.render(e)).collect::<Vec<_>>().join(" "))
    }
}

fn ty_sym(e: &Elab, t: TyId) -> String {
    let ti = &e.g.tys[t.0 as usize];
    sym(&format!("{}.{}", ti.module, ti.name))
}

fn con_sym(e: &Elab, c: ConId) -> String {
    let ci = &e.g.cons[c.0 as usize];
    let ti = &e.g.tys[ci.ty.0 as usize];
    sym(&format!("{}.{}", ti.module, ci.name))
}

/// The recognizer of constructor `c`. Z3 names it `is-C` and resolves it by
/// its argument's sort; `(_ is C)` is ambiguous once a parametric datatype is
/// used at two sorts.
fn tester(e: &Elab, c: ConId) -> String {
    let ci = &e.g.cons[c.0 as usize];
    let ti = &e.g.tys[ci.ty.0 as usize];
    sym(&format!("is-{}.{}", ti.module, ci.name))
}

fn sel_sym(e: &Elab, c: ConId, k: usize) -> String {
    let ci = &e.g.cons[c.0 as usize];
    let ti = &e.g.tys[ci.ty.0 as usize];
    sym(&format!("{}.{}.{}", ti.module, ci.name, k))
}

fn tuple_sym(n: usize) -> String {
    format!("|Tuple{n}|")
}

fn tuple_con(n: usize) -> String {
    format!("|tuple{n}|")
}

fn tuple_sel(n: usize, k: usize) -> String {
    format!("|tuple{n}.{k}|")
}

/// What a de Bruijn variable stands for during translation.
#[derive(Clone)]
enum Ent {
    /// A term of the given sort.
    Term(String, Sort),
    /// A type: the sort it denotes.
    Ty(Sort),
    /// A local function: name, argument sorts, result sort.
    Fun(String, Vec<Sort>, Sort),
    /// Something the solver can't see (a value only used in types).
    Opaque(String),
    /// A known function value: a closed term (a top-level function or a
    /// lambda without free variables), keyed for instance names.
    Known(String),
}

impl fmt::Debug for Ent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ent::Term(t, _) => write!(f, "{t}"),
            Ent::Ty(_) => write!(f, "<type>"),
            Ent::Fun(n, ..) => write!(f, "{n}"),
            Ent::Known(k) => write!(f, "{k}"),
            Ent::Opaque(w) => write!(f, "<{w}>"),
        }
    }
}

/// A use of a function at a sort instance.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Inst {
    def: DefId,
    tys: Vec<Sort>,
    /// Keys of known function arguments (higher-order specialization).
    funs: Vec<String>,
}

/// An application whose postcondition should be assumed.
/// A reflected instance's definition: name, `define-funs-rec` head, body.
type Defn = (String, String, String);
/// An instance's environment, parameters and result sort.
type InstSig = (Vec<Ent>, Vec<(String, Sort)>, Sort);

struct PostUse {
    def: DefId,
    env: Vec<Ent>,
    /// The result is a `Nat`: assumed where the precondition holds.
    nat: bool,
}

/// What it takes to reflect only some definitions: the declarations that
/// aren't reflected anyway, and each reflected one (name, head, body, its
/// uninterpreted declaration).
pub struct Focus {
    others: Vec<String>,
    group: Vec<(String, String, String, Option<String>)>,
}

impl Focus {
    /// Reflect the definitions `goal` mentions; leave the rest
    /// uninterpreted. `None` if that is all or none of them.
    fn for_goal(&self, goal: &str) -> Option<String> {
        let (on, off): (Vec<_>, Vec<_>) = self.group.iter().partition(|(n, ..)| goal.contains(n.as_str()));
        if on.is_empty() || off.is_empty() {
            return None;
        }
        let mut out = String::new();
        for d in &self.others {
            out += d;
            out += "\n";
        }
        for (_, _, _, d) in &off {
            out += d.as_deref()?;
            out += "\n";
        }
        let heads: Vec<&str> = on.iter().map(|g| g.1.as_str()).collect();
        let bodies: Vec<&str> = on.iter().map(|g| g.2.as_str()).collect();
        out += &format!("(define-funs-rec ({}) ({}))\n", heads.join(" "), bodies.join(" "));
        Some(out)
    }
}

pub struct Query {
    pub text: String,
    /// The same query without the quantified `Nat` axioms: Z3 is complete on
    /// it, so it can find a counterexample where the full query is `unknown`.
    pub without_axioms: Option<String>,
    /// The same query with every reflected definition uninterpreted: weaker,
    /// so `unsat` still proves the goal, and often far faster when the facts
    /// in scope (`have`) already suffice. Tried first.
    pub facts_only: Option<String>,
    /// Only the definitions the goal mentions reflected, without the
    /// quantified axioms: weaker again, and Z3 doesn't unfold functions
    /// whose results the facts in scope already give (M12).
    pub focused: Option<String>,
    /// Why facts in scope could not be given to the solver.
    pub dropped: Vec<String>,
    /// (SMT name, display name) of the locals, for a counterexample.
    pub shown: Vec<(String, String)>,
    /// The SMT names of `String` locals (shown as text, not bytes).
    pub string_vars: Vec<String>,
}

/// What defining an instance added to a builder, so another builder for the
/// same module can reuse the translation (M12: the definitions are the same
/// for every obligation; translating them was most of a cached check).
#[derive(Clone, Default)]
struct Delta {
    datatypes: Vec<(TyId, usize)>,
    tuples: Vec<usize>,
    sorts: Vec<(String, usize)>,
    funs: Vec<(String, String)>,
    insts: Vec<Inst>,
    known: Vec<(String, Tm)>,
    axioms: Vec<(String, String)>,
    asserts: Vec<String>,
    consts: Vec<String>,
}

/// Translated definitions, shared by the builders of one module.
#[derive(Default)]
pub struct Defs(std::cell::RefCell<BTreeMap<Inst, (Tx<Defn>, Delta)>>);

pub struct Builder<'a> {
    e: &'a Elab,
    defs: Option<&'a Defs>,
    user: String,
    datatypes: BTreeMap<TyId, usize>,
    tuples: HashSet<usize>,
    sorts: BTreeMap<String, usize>,
    /// Uninterpreted functions: name → declaration.
    funs: BTreeMap<String, String>,
    /// A local function's type, over the locals before it (D84).
    fun_tys: BTreeMap<String, (usize, Tm)>,
    /// Reflected instances waiting for / with a definition.
    insts: BTreeMap<Inst, Option<Defn>>,
    /// Known function values by key.
    known: BTreeMap<String, Tm>,
    inst_queue: Vec<Inst>,
    consts: Vec<String>,
    asserts: Vec<String>,
    /// `Nat` results of functions, as pattern-guarded axioms (emitted after the definitions).
    axioms: BTreeMap<String, String>,
    posts: Vec<PostUse>,
    post_seen: HashSet<String>,
    nat_seen: HashSet<String>,
    /// Translating a reflected body: don't collect postconditions or facts.
    in_def: bool,
    ctx: Vec<Option<Ent>>,
    ctx_src: Vec<ObLocal>,
    pub shown: Vec<(String, String)>,
    string_vars: Vec<String>,
}

impl<'a> Builder<'a> {
    pub fn new(e: &'a Elab, user: &str) -> Builder<'a> {
        Builder {
            e,
            defs: None,
            user: user.to_string(),
            datatypes: BTreeMap::new(),
            tuples: HashSet::new(),
            sorts: BTreeMap::new(),
            funs: BTreeMap::new(),
            fun_tys: BTreeMap::new(),
            insts: BTreeMap::new(),
            known: BTreeMap::new(),
            inst_queue: Vec::new(),
            consts: Vec::new(),
            asserts: Vec::new(),
            axioms: BTreeMap::new(),
            posts: Vec::new(),
            post_seen: HashSet::new(),
            nat_seen: HashSet::new(),
            in_def: false,
            ctx: Vec::new(),
            ctx_src: Vec::new(),
            shown: Vec::new(),
            string_vars: Vec::new(),
        }
    }

    /// Share translated definitions with the other builders of the module.
    pub fn sharing(mut self, defs: &'a Defs) -> Builder<'a> {
        self.defs = Some(defs);
        self
    }

    /// `define`, reusing another builder's translation. A translation is
    /// recorded with everything it refers to (sorts, declarations,
    /// instances), translating it in an empty builder, so replaying it is
    /// enough wherever it is used.
    fn define_shared(&mut self, inst: &Inst) -> Tx<Defn> {
        let Some(defs) = self.defs else { return self.define(inst) };
        let found = defs.0.borrow().get(inst).cloned();
        let (r, d) = match found {
            Some(x) => x,
            None => {
                let saved = (
                    std::mem::take(&mut self.datatypes),
                    std::mem::take(&mut self.tuples),
                    std::mem::take(&mut self.sorts),
                    std::mem::take(&mut self.funs),
                    std::mem::take(&mut self.insts),
                    std::mem::take(&mut self.inst_queue),
                    std::mem::take(&mut self.axioms),
                    std::mem::take(&mut self.asserts),
                    std::mem::take(&mut self.consts),
                );
                let known_before: HashSet<String> = self.known.keys().cloned().collect();
                let r = self.define(inst);
                let d = Delta {
                    datatypes: std::mem::replace(&mut self.datatypes, saved.0).into_iter().collect(),
                    tuples: std::mem::replace(&mut self.tuples, saved.1).into_iter().collect(),
                    sorts: std::mem::replace(&mut self.sorts, saved.2).into_iter().collect(),
                    funs: std::mem::replace(&mut self.funs, saved.3).into_iter().collect(),
                    insts: std::mem::replace(&mut self.insts, saved.4).into_keys().collect(),
                    known: self.known.iter().filter(|(k, _)| !known_before.contains(*k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
                    axioms: std::mem::replace(&mut self.axioms, saved.6).into_iter().collect(),
                    asserts: std::mem::replace(&mut self.asserts, saved.7),
                    consts: std::mem::replace(&mut self.consts, saved.8),
                };
                self.inst_queue = saved.5;
                defs.0.borrow_mut().insert(inst.clone(), (r.clone(), d.clone()));
                (r, d)
            }
        };
        self.datatypes.extend(d.datatypes);
        self.tuples.extend(d.tuples);
        self.sorts.extend(d.sorts);
        for (k, v) in d.funs {
            self.funs.entry(k).or_insert(v);
        }
        for i in d.insts {
            if &i != inst && !self.insts.contains_key(&i) {
                self.insts.insert(i.clone(), None);
                self.inst_queue.push(i);
            }
        }
        for (k, v) in d.known {
            self.known.entry(k).or_insert(v);
        }
        for (k, v) in d.axioms {
            self.axioms.entry(k).or_insert(v);
        }
        for a in d.asserts {
            if !self.asserts.contains(&a) {
                self.asserts.push(a);
            }
        }
        for c in d.consts {
            if !self.consts.contains(&c) {
                self.consts.push(c);
            }
        }
        r
    }

    fn wk(&self) -> &crate::core::WellKnown {
        &self.e.g.well_known
    }

    // ── sorts ───────────────────────────────────────────────────────────────

    /// Replace solved unknowns (`?m a xs`, as elaboration leaves them) by
    /// their solutions, by evaluating over neutral variables.
    fn zonk(&self, n: usize, t: &Tm) -> Tm {
        if !has_meta(t) {
            return t.clone();
        }
        let env = Rc::new((0..n).map(Val::var).collect::<Vec<_>>());
        quote(&self.e.g, n, &eval(&self.e.g, &env, t))
    }

    /// Is this binder's type `Type` (possibly through a solved unknown)?
    fn is_type(&self, t: &Tm) -> bool {
        match t {
            Tm::Univ(_) => true,
            _ if has_meta(t) => {
                let n = max_var(t).map_or(0, |m| m + 1);
                matches!(self.zonk(n, t), Tm::Univ(_))
            }
            _ => false,
        }
    }

    fn is_bag(&self, t: TyId) -> bool {
        let ti = &self.e.g.tys[t.0 as usize];
        &*ti.module == "std.bag" && &*ti.name == "Bag"
    }

    /// The sort a type term denotes, in `env`.
    fn sort_of(&mut self, env: &[Ent], t: &Tm) -> Tx<Sort> {
        let wk = self.wk().clone();
        let z = self.zonk(env.len(), t);
        let t = &z;
        match t {
            Tm::Var(i) => match self.resolve(env, *i)? {
                Ent::Ty(s) => Ok(s),
                _ => out("a type that depends on a value"),
            },
            Tm::Meta(m) => match self.e.g.meta(*m) {
                Some(v) => {
                    let tm = quote(&self.e.g, env.len(), &v);
                    self.sort_of(env, &tm)
                }
                None => out("a type the checker could not work out"),
            },
            Tm::TupleTy(ts) => {
                let mut ss = Vec::new();
                for t in ts {
                    ss.push(self.sort_of(env, t)?);
                }
                self.tuples.insert(ss.len());
                Ok(Sort::Tuple(ss))
            }
            Tm::TyCon(_) | Tm::TyConApp(..) | Tm::App(..) | Tm::Def(_) => {
                let mut args = Vec::new();
                let mut h = t;
                while let Tm::App(f, a, _, _) = h {
                    args.push((**a).clone());
                    h = f;
                }
                args.reverse();
                match h {
                    Tm::TyConApp(id, v) => {
                        let mut all = v.clone();
                        all.extend(args);
                        self.ty_sort(env, *id, &all)
                    }
                    Tm::TyCon(id) => self.ty_sort(env, *id, &args),
                    Tm::Def(d) => {
                        // A type alias: unfold it.
                        let Some(body) = self.e.g.defs[d.0 as usize].body.clone() else {
                            return out("an abstract type definition");
                        };
                        let mut b = &body;
                        let mut inner: Vec<Ent> = Vec::new();
                        let mut k = 0;
                        while let Tm::Lam(_, _, _, x) = b {
                            let s = match args.get(k) {
                                Some(a) => self.sort_of(env, a).map(Ent::Ty).unwrap_or(Ent::Opaque("arg".into())),
                                None => return out("a partially applied type"),
                            };
                            inner.push(s);
                            b = x;
                            k += 1;
                        }
                        let b = b.clone();
                        self.sort_of(&inner, &b)
                    }
                    _ => out("an unsupported type"),
                }
            }
            _ if wk.nat.is_none() => out("no prelude"),
            Tm::Pi(..) => out("a function type"),
            Tm::Univ(_) => out("a universe"),
            _ => out("an unsupported type"),
        }
    }

    fn ty_sort(&mut self, env: &[Ent], id: TyId, args: &[Tm]) -> Tx<Sort> {
        let wk = self.wk().clone();
        if Some(id) == wk.nat || Some(id) == wk.int {
            return Ok(Sort::Int);
        }
        if Some(id) == wk.bool_ty {
            return Ok(Sort::Bool);
        }
        if Some(id) == wk.string {
            return Ok(Sort::Str);
        }
        if Some(id) == wk.bytes {
            return Ok(Sort::Bytes);
        }
        if self.is_bag(id) {
            return Ok(Sort::Bag);
        }
        // Only type parameters (of kind `Type`) become sort parameters.
        let params = self.e.g.tys[id.0 as usize].params.clone();
        let mut sargs = Vec::new();
        for (k, (_, pty)) in params.iter().enumerate() {
            if self.is_type(pty) {
                let a = args.get(k).ok_or_else(|| Outside("a partially applied type".into()))?;
                sargs.push(self.sort_of(env, a)?);
            }
        }
        let ti = &self.e.g.tys[id.0 as usize];
        if ti.ctors.is_empty() {
            let name = format!("{}.{}", ti.module, ti.name);
            self.sorts.insert(name.clone(), sargs.len());
            return Ok(Sort::Unin(name, sargs));
        }
        let n = sargs.len();
        if let std::collections::btree_map::Entry::Vacant(e) = self.datatypes.entry(id) {
            e.insert(n);
            // Register the field types' datatypes too.
            self.datatype_decl(id)?;
        }
        Ok(Sort::Data(id, sargs))
    }

    /// The parameter environment of a datatype declaration: type parameters
    /// are the sort variables `T0, T1, …`; value parameters are opaque.
    fn decl_env(&self, id: TyId) -> Vec<Ent> {
        let params = &self.e.g.tys[id.0 as usize].params;
        let mut k = 0;
        params
            .iter()
            .map(|(_, t)| {
                if self.is_type(t) {
                    k += 1;
                    Ent::Ty(Sort::Unin(format!("T{}", k - 1), vec![]))
                } else {
                    Ent::Opaque("value parameter".into())
                }
            })
            .collect()
    }

    /// The SMT fields of a constructor: (field index, sort), skipping type-valued fields.
    fn con_fields(&mut self, c: ConId, env: &[Ent]) -> Tx<Vec<(usize, Sort)>> {
        let fields = self.e.g.cons[c.0 as usize].fields.clone();
        let mut env = env.to_vec();
        let mut out_ = Vec::new();
        for (k, f) in fields.iter().enumerate() {
            match &f.3 {
                ty if self.is_type(ty) => env.push(Ent::Ty(Sort::Unin("field".into(), vec![]))),
                ty => {
                    let s = self.sort_of(&env, ty)?;
                    out_.push((k, s.clone()));
                    env.push(Ent::Term(String::new(), s));
                }
            }
        }
        Ok(out_)
    }

    fn datatype_decl(&mut self, id: TyId) -> Tx<()> {
        let env = self.decl_env(id);
        for c in self.e.g.tys[id.0 as usize].ctors.clone() {
            self.con_fields(c, &env)?;
        }
        Ok(())
    }

    fn sort_decls(&mut self) -> Tx<Vec<String>> {
        let mut out_ = Vec::new();
        for (name, n) in &self.sorts {
            out_.push(format!("(declare-sort {} {n})", sym(name)));
        }
        // Each declaration: (head, body, the heads its fields mention).
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum Head {
            Tuple(usize),
            Data(TyId),
        }
        fn mentions(s: &Sort, out_: &mut BTreeSet<Head>) {
            match s {
                Sort::Data(t, args) => {
                    out_.insert(Head::Data(*t));
                    args.iter().for_each(|a| mentions(a, out_));
                }
                Sort::Tuple(xs) => {
                    out_.insert(Head::Tuple(xs.len()));
                    xs.iter().for_each(|a| mentions(a, out_));
                }
                Sort::Unin(_, xs) => xs.iter().for_each(|a| mentions(a, out_)),
                _ => {}
            }
        }
        let mut decls: BTreeMap<Head, (String, String, BTreeSet<Head>)> = BTreeMap::new();
        for &n in &self.tuples {
            let ps: Vec<String> = (0..n).map(|k| format!("T{k}")).collect();
            let fields: Vec<String> = (0..n).map(|k| format!("({} T{k})", tuple_sel(n, k))).collect();
            let ctor = format!("({} {})", tuple_con(n), fields.join(" "));
            let body = if n == 0 { format!("(({}))", tuple_con(0)) } else { format!("(par ({}) ({ctor}))", ps.join(" ")) };
            decls.insert(Head::Tuple(n), (format!("({} {n})", tuple_sym(n)), body, BTreeSet::new()));
        }
        let ids: Vec<(TyId, usize)> = self.datatypes.iter().map(|(a, b)| (*a, *b)).collect();
        for (id, n) in ids {
            let env = self.decl_env(id);
            let mut ctors = Vec::new();
            let mut deps = BTreeSet::new();
            for c in self.e.g.tys[id.0 as usize].ctors.clone() {
                let fs = self.con_fields(c, &env)?;
                fs.iter().for_each(|(_, s)| mentions(s, &mut deps));
                let fields: Vec<String> =
                    fs.iter().map(|(k, s)| format!("({} {})", sel_sym(self.e, c, *k), s.render(self.e))).collect();
                ctors.push(if fields.is_empty() {
                    format!("({})", con_sym(self.e, c))
                } else {
                    format!("({} {})", con_sym(self.e, c), fields.join(" "))
                });
            }
            let ps: Vec<String> = (0..n).map(|k| format!("T{k}")).collect();
            let body = if n == 0 {
                format!("({})", ctors.join(" "))
            } else {
                format!("(par ({}) ({}))", ps.join(" "), ctors.join(" "))
            };
            decls.insert(Head::Data(id), (format!("({} {n})", ty_sym(self.e, id)), body, deps));
        }
        // Z3 rejects a group whose members use a sibling at other parameters
        // (`List (Tuple2 String Json)` beside `Json`), so declare each strongly
        // connected group on its own, dependencies first.
        let keys: Vec<Head> = decls.keys().copied().collect();
        let reach = |from: Head| -> BTreeSet<Head> {
            let mut seen = BTreeSet::new();
            let mut stack = vec![from];
            while let Some(h) = stack.pop() {
                for d in decls.get(&h).map(|x| x.2.clone()).unwrap_or_default() {
                    if decls.contains_key(&d) && seen.insert(d) {
                        stack.push(d);
                    }
                }
            }
            seen
        };
        let reaches: BTreeMap<Head, BTreeSet<Head>> = keys.iter().map(|&k| (k, reach(k))).collect();
        let mut done: BTreeSet<Head> = BTreeSet::new();
        while done.len() < keys.len() {
            // A group whose dependencies outside itself are all declared.
            let mut progressed = false;
            for &k in &keys {
                if done.contains(&k) {
                    continue;
                }
                let group: Vec<Head> = keys
                    .iter()
                    .copied()
                    .filter(|&j| j == k || (reaches[&k].contains(&j) && reaches[&j].contains(&k)))
                    .collect();
                let ready = reaches[&k].iter().all(|d| done.contains(d) || group.contains(d));
                if !ready {
                    continue;
                }
                let heads: Vec<&str> = group.iter().map(|h| decls[h].0.as_str()).collect();
                let bodies: Vec<&str> = group.iter().map(|h| decls[h].1.as_str()).collect();
                out_.push(format!("(declare-datatypes ({}) ({}))", heads.join(" "), bodies.join(" ")));
                done.extend(group);
                progressed = true;
            }
            if !progressed {
                return out("cyclic datatype declarations");
            }
        }
        Ok(out_)
    }

    // ── terms ───────────────────────────────────────────────────────────────

    fn local(&mut self, lvl: usize) -> Tx<Ent> {
        if let Some(Some(e)) = self.ctx.get(lvl) {
            return Ok(e.clone());
        }
        let l = self.ctx_src[lvl].clone();
        let env: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let ty = force(&self.e.g, l.ty.clone());
        let name = sym(&format!("{}#{lvl}", l.name));
        let ent = match &ty {
            Val::Univ(_) => {
                let s = format!("{}#{lvl}", l.name);
                self.sorts.insert(s.clone(), 0);
                Ent::Ty(Sort::Unin(s, vec![]))
            }
            Val::Pi(..) => {
                // A local function: uninterpreted, if its type is simple.
                let mut args = Vec::new();
                let mut t = quote(&self.e.g, lvl, &ty);
                let mut inner = env.clone();
                while let Tm::Pi(_, m, _, a, b) = t.clone() {
                    let s = self.sort_of(&inner, &a)?;
                    if m != Mult::Zero {
                        args.push(s.clone());
                    }
                    inner.push(Ent::Opaque("arg".into()));
                    t = (*b).clone();
                }
                let r = self.sort_of(&inner, &t)?;
                let decl = format!(
                    "(declare-fun {name} ({}) {})",
                    args.iter().map(|s| s.render(self.e)).collect::<Vec<_>>().join(" "),
                    r.render(self.e)
                );
                self.funs.insert(name.clone(), decl);
                self.fun_tys.insert(name.clone(), (lvl, quote(&self.e.g, lvl, &ty)));
                Ent::Fun(name, args, r)
            }
            _ => {
                let tyt = quote(&self.e.g, lvl, &ty);
                let s = self.sort_of(&env, &tyt)?;
                self.consts.push(format!("(declare-const {name} {})", s.render(self.e)));
                if self.is_nat_val(&l.ty) {
                    self.asserts.push(format!("(>= {name} 0)"));
                }
                // A value of a datatype carries its constructor's invariants (D11).
                // A refinement alias (`U8`) brings its predicates.
                let raw = quote(&self.e.g, lvl, &l.ty);
                self.alias_facts(&env, &raw, &name, &s);
                if let Sort::Data(id, sargs) = &s {
                    let vals = self.value_args(&env, &tyt);
                    self.datatype_facts(&name, *id, sargs, &vals);
                    // A field at a type parameter instantiated with a
                    // refinement alias (`Parsed Members …`) has its predicates.
                    self.field_alias_facts(&env, &raw, &name, *id, sargs);
                }
                if !l.name.starts_with('$') && !l.name.starts_with('_') {
                    self.shown.push((name.clone(), l.name.to_string()));
                    if s == Sort::Str {
                        self.string_vars.push(name.clone());
                    }
                }
                Ent::Term(name.clone(), s)
            }
        };
        self.ctx[lvl] = Some(ent.clone());
        // A `let`-bound local equals its value.
        if let (Some(def), Ent::Term(n, _)) = (&l.def, &ent) {
            let tm = quote(&self.e.g, lvl, def);
            if let Ok((v, _)) = self.term_ctx(lvl, &tm) {
                self.asserts.push(format!("(= {n} {v})"));
            }
        }
        Ok(ent)
    }

    /// For each constructor of `id`: if `x` is that constructor, its `Nat`
    /// fields are non-negative and its invariants hold.
    /// If `ty` is a refinement alias, assert its predicates about `x`.
    fn alias_facts(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) {
        let ts = self.alias_terms(env, ty, x, xs);
        self.asserts.extend(ts);
    }

    /// A call `f a…` of a local function whose type is refined (D84): where
    /// its preconditions hold at the arguments, its postconditions hold at
    /// the result.
    fn fun_post_facts(&mut self, env: &[Ent], name: &str, args: &[(Tm, Mult)], app: &str, rs: &Sort) {
        let Some((lvl, ty)) = self.fun_tys.get(name).cloned() else { return };
        let mut inner: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let mut pres = Vec::new();
        let mut t = ty;
        for (a, m) in args {
            let Tm::Pi(_, _, _, dom, cod) = t else { return };
            if *m == Mult::Zero {
                inner.push(Ent::Opaque("type argument".into()));
            } else {
                let Ok((at, s)) = self.term(env, a) else { return };
                pres.extend(self.alias_terms(&inner, &dom, &at, &s));
                inner.push(Ent::Term(at, s));
            }
            t = (*cod).clone();
        }
        let posts = self.alias_terms(&inner, &t, app, rs);
        if posts.is_empty() {
            return;
        }
        let post = if posts.len() == 1 { posts[0].clone() } else { format!("(and {})", posts.join(" ")) };
        self.asserts.push(match pres.len() {
            0 => post,
            1 => format!("(=> {} {post})", pres[0]),
            _ => format!("(=> (and {}) {post})", pres.join(" ")),
        });
    }

    /// The predicates of the refinement alias `ty` at `x`, as terms.
    fn alias_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) -> Vec<String> {
        let mut args = Vec::new();
        let mut h = ty;
        while let Tm::App(f, a, _, _) = h {
            args.push((**a).clone());
            h = f;
        }
        args.reverse();
        let Tm::Def(d) = h else { return Vec::new() };
        let Some(preds) = self.e.alias_preds.get(d).cloned() else { return Vec::new() };
        let mut inner = Vec::new();
        for a in &args {
            inner.push(match self.sort_of(env, a) {
                Ok(s) if self.is_type(a) => Ent::Ty(s),
                _ => match self.term(env, a) {
                    Ok((t, s)) => Ent::Term(t, s),
                    Err(_) => Ent::Opaque("alias argument".into()),
                },
            });
        }
        inner.push(Ent::Term(x.to_string(), xs.clone()));
        let mut out = Vec::new();
        for p in preds {
            if let Ok((t, Sort::Bool)) = self.term(&inner, &p.tm) {
                out.push(t);
            }
        }
        out
    }

    fn field_alias_facts(&mut self, env: &[Ent], ty: &Tm, x: &str, id: TyId, sargs: &[Sort]) {
        let mut args = Vec::new();
        let mut h = ty;
        while let Tm::App(f, a, _, _) = h {
            args.push((**a).clone());
            h = f;
        }
        args.reverse();
        if let Tm::TyConApp(_, v) = h {
            let mut all = v.clone();
            all.extend(args);
            args = all;
        }
        if !args.iter().any(|a| matches!(a, Tm::Def(_) | Tm::App(..))) {
            return;
        }
        let ctors = self.e.g.tys[id.0 as usize].ctors.clone();
        if ctors.len() != 1 {
            return;
        }
        let c = ctors[0];
        let n = self.e.g.tys[id.0 as usize].params.len();
        let senv = self.sort_env(id, sargs);
        let Ok(fs) = self.con_fields(c, &senv) else { return };
        let fields = self.e.g.cons[c.0 as usize].fields.clone();
        for (k, f) in fields.iter().enumerate() {
            let Tm::Var(i) = f.3 else { continue };
            let Some(level) = (n + k).checked_sub(1 + i) else { continue };
            let (Some(arg), Some((_, fsort))) = (args.get(level), fs.iter().find(|(j, _)| *j == k)) else { continue };
            if level >= n {
                continue;
            }
            let sel = format!("({} {x})", sel_sym(self.e, c, k));
            let (arg, fsort) = (arg.clone(), fsort.clone());
            self.alias_facts(env, &arg, &sel, &fsort);
        }
    }

    /// The value arguments of a datatype type (`Parsed Json src i` → `src`,
    /// `i`), translated where possible, by parameter position.
    fn value_args(&mut self, env: &[Ent], ty: &Tm) -> Vec<Option<(String, Sort)>> {
        let mut args = Vec::new();
        let mut h = ty;
        while let Tm::App(f, a, _, _) = h {
            args.push((**a).clone());
            h = f;
        }
        args.reverse();
        let id = match h {
            Tm::TyConApp(id, v) => {
                let mut all = v.clone();
                all.extend(args);
                args = all;
                *id
            }
            Tm::TyCon(id) => *id,
            _ => return Vec::new(),
        };
        let params = self.e.g.tys[id.0 as usize].params.clone();
        let mut out_ = Vec::new();
        for (k, (_, pty)) in params.iter().enumerate() {
            out_.push(match args.get(k) {
                Some(a) if !self.is_type(pty) => self.term(env, a).ok(),
                _ => None,
            });
        }
        out_
    }

    fn datatype_facts(&mut self, x: &str, id: TyId, sargs: &[Sort], vals: &[Option<(String, Sort)>]) {
        let mut senv = self.sort_env(id, sargs);
        // Invariants may mention the type's value parameters (`stop <= len src`).
        for (k, v) in vals.iter().enumerate() {
            if let (Some((t, s)), Some(slot @ Ent::Opaque(_))) = (v, senv.get_mut(k)) {
                *slot = Ent::Term(t.clone(), s.clone());
            }
        }
        let ctors = self.e.g.tys[id.0 as usize].ctors.clone();
        for c in ctors {
            let Ok(fs) = self.con_fields(c, &senv) else { continue };
            let fields = self.e.g.cons[c.0 as usize].fields.clone();
            let mut env = senv.clone();
            let mut facts = Vec::new();
            for (k, f) in fields.iter().enumerate() {
                match fs.iter().find(|(i, _)| *i == k) {
                    Some((_, fsort)) => {
                        let sel = format!("({} {x})", sel_sym(self.e, c, k));
                        if self.is_nat_tm(&f.3) {
                            facts.push(format!("(>= {sel} 0)"));
                        }
                        env.push(Ent::Term(sel, fsort.clone()));
                    }
                    None => env.push(Ent::Ty(Sort::Unin("field".into(), vec![]))),
                }
            }
            for inv in self.e.con_invs.get(&c).cloned().unwrap_or_default() {
                let saved = self.in_def;
                self.in_def = true;
                if let Ok((t, Sort::Bool)) = self.term(&env, &inv.tm) {
                    facts.push(t);
                }
                self.in_def = saved;
            }
            if facts.is_empty() {
                continue;
            }
            let all = if facts.len() == 1 { facts[0].clone() } else { format!("(and {})", facts.join(" ")) };
            let only = self.e.g.tys[id.0 as usize].ctors.len() == 1;
            self.asserts.push(if only { all } else { format!("(=> ({} {x}) {all})", tester(self.e, c)) });
        }
    }

    /// Translate a term over the first `lvl` obligation locals.
    fn term_ctx(&mut self, lvl: usize, t: &Tm) -> Tx<(String, Sort)> {
        let mut env = Vec::with_capacity(lvl);
        for k in 0..lvl {
            env.push(Ent::Opaque(format!("@{k}")));
        }
        // Locals are resolved lazily through `@k` markers.
        self.term(&env, t)
    }

    fn resolve(&mut self, env: &[Ent], i: usize) -> Tx<Ent> {
        match env.get(env.len().wrapping_sub(1 + i)) {
            Some(Ent::Opaque(m)) if m.starts_with('@') => {
                let lvl: usize = m[1..].parse().unwrap_or(0);
                self.local(lvl)
            }
            Some(e) => Ok(e.clone()),
            None => out("an unbound variable"),
        }
    }

    fn is_nat_val(&self, ty: &Val) -> bool {
        matches!(force(&self.e.g, ty.clone()), Val::TyCon(t, _) if Some(t) == self.e.g.well_known.nat)
    }

    fn is_nat_tm(&self, ty: &Tm) -> bool {
        let mut h = ty;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        match h {
            Tm::TyCon(t) | Tm::TyConApp(t, _) => Some(*t) == self.e.g.well_known.nat,
            Tm::Def(d) => match &self.e.g.defs[d.0 as usize].body {
                Some(b) => {
                    let mut b = b;
                    while let Tm::Lam(_, _, _, x) = b {
                        b = x;
                    }
                    self.is_nat_tm(b)
                }
                None => false,
            },
            Tm::Meta(m) => self.e.g.meta(*m).is_some_and(|v| self.is_nat_val(&v)),
            _ => false,
        }
    }

    /// Every result of `f` is a `Nat`: `∀ args. f args >= 0`, instantiated by
    /// Z3 for each `f` term, including those it makes by unfolding definitions.
    fn nat_axiom(&mut self, name: &str, args: &[String]) {
        let ax = if args.is_empty() {
            format!("(>= {name} 0)")
        } else {
            let vars: Vec<String> = (0..args.len()).map(|k| format!("a{k}")).collect();
            let binds: Vec<String> = vars.iter().zip(args).map(|(v, s)| format!("({v} {s})")).collect();
            let app = format!("({name} {})", vars.join(" "));
            format!("(forall ({}) (! (>= {app} 0) :pattern ({app})))", binds.join(" "))
        };
        self.axioms.insert(name.to_string(), ax);
    }

    /// Is `d`'s result `>= 0` for every solver value of its arguments? For
    /// a declared (uninterpreted) `Nat` function, assuming so is consistent.
    /// For a reflected one, its body must be built from non-negative parts
    /// (`0`, `1 + length rest`), with no precondition, and any recursion
    /// structural: the unfolding is then finite on every solver value, so
    /// the claim follows by induction. (`decreasing` recursion may run
    /// forever on values the program can't build, so it gets no axiom.)
    fn nonneg_fn(&self, d: DefId, stack: &mut Vec<DefId>) -> bool {
        let mut ty = self.e.g.defs[d.0 as usize].ty.clone();
        while let Tm::Pi(_, _, _, _, b) = ty {
            ty = (*b).clone();
        }
        if !self.is_nat_tm(&ty) {
            return false;
        }
        if !self.reflected(d) {
            return true;
        }
        let spec = self.e.specs.get(&d);
        if spec.is_some_and(|s| s.measure.is_some() || s.preds.iter().any(|p| !p.is_post)) {
            return false;
        }
        if stack.contains(&d) {
            return true;
        }
        let Some(mut body) = self.e.g.defs[d.0 as usize].body.clone() else { return false };
        while let Tm::Lam(_, _, _, b) = body {
            body = (*b).clone();
        }
        stack.push(d);
        let r = self.nonneg(&body, stack);
        stack.pop();
        r
    }

    /// `t` is `>= 0` for every solver value of its free variables.
    fn nonneg(&self, t: &Tm, stack: &mut Vec<DefId>) -> bool {
        match t {
            Tm::Lit(Lit::Num(n)) => *n >= 0,
            Tm::PrimApp(Prim::Add | Prim::Mul, xs) => xs.iter().all(|x| self.nonneg(x, stack)),
            Tm::PrimApp(Prim::Len, _) => true,
            Tm::PrimApp(Prim::Par, xs) => xs.iter().all(|x| self.nonneg(x, stack)),
            Tm::Let(_, _, _, _, b) => self.nonneg(b, stack),
            Tm::Case(_, c) => {
                c.branches.iter().all(|(_, _, b)| matches!(b, Tm::Error) || self.nonneg(b, stack))
                    && c.lits.iter().all(|(_, b)| matches!(b, Tm::Error) || self.nonneg(b, stack))
                    && c.default.as_ref().is_none_or(|b| matches!(b, Tm::Error) || self.nonneg(b, stack))
            }
            Tm::App(..) | Tm::Def(_) => {
                let mut h = t;
                while let Tm::App(f, ..) = h {
                    h = f;
                }
                let Tm::Def(d) = h else { return false };
                self.nonneg_fn(*d, stack)
            }
            _ => false,
        }
    }

    fn nat_fact(&mut self, t: &str) {
        if !self.in_def && self.nat_seen.insert(t.to_string()) {
            self.asserts.push(format!("(>= {t} 0)"));
        }
    }

    fn term(&mut self, env: &[Ent], t: &Tm) -> Tx<(String, Sort)> {
        match t {
            Tm::Var(i) => match self.resolve(env, *i)? {
                Ent::Term(n, s) => Ok((n, s)),
                Ent::Fun(n, a, r) if a.is_empty() => Ok((n, r)),
                Ent::Fun(..) => out("a function used as a value"),
                Ent::Ty(_) => out("a type used as a value"),
                Ent::Known(_) => out("a function used as a value"),
                Ent::Opaque(w) => out(format!("a value the prover can't see ({w})")),
            },
            Tm::Meta(m) => match self.e.g.meta(*m) {
                Some(v) => {
                    let tm = quote(&self.e.g, env.len(), &v);
                    self.term(env, &tm)
                }
                None => out("an unsolved unknown"),
            },
            Tm::Lit(Lit::Num(n)) => Ok((if *n < 0 { format!("(- {})", -n) } else { n.to_string() }, Sort::Int)),
            Tm::Lit(Lit::Str(s)) => {
                Ok((smt_bytes(s.as_bytes()), Sort::Str))
            }
            Tm::Lit(Lit::Bytes(b)) => Ok((smt_bytes(b), Sort::Bytes)),
            Tm::Tuple(xs) => {
                let mut ts = Vec::new();
                let mut ss = Vec::new();
                for x in xs {
                    let (t, s) = self.term(env, x)?;
                    ts.push(t);
                    ss.push(s);
                }
                self.tuples.insert(xs.len());
                let sort = Sort::Tuple(ss);
                if xs.is_empty() {
                    Ok((tuple_con(0), sort))
                } else {
                    Ok((format!("({} {})", tuple_con(xs.len()), ts.join(" ")), sort))
                }
            }
            Tm::Proj(x, i) => {
                let (xt, xs) = self.term(env, x)?;
                match xs {
                    Sort::Tuple(ss) => {
                        let s = ss.get(*i).cloned().ok_or_else(|| Outside("a bad projection".into()))?;
                        let t = format!("({} {xt})", tuple_sel(ss.len(), *i));
                        Ok((t, s))
                    }
                    _ => out("a projection from a non-tuple"),
                }
            }
            Tm::Field(x, c, i) => {
                let (xt, xs) = self.term(env, x)?;
                let Sort::Data(_, sargs) = &xs else { return out("a field of a non-record") };
                let fs = self.con_fields(*c, &self.sort_env(self.e.g.cons[c.0 as usize].ty, sargs))?;
                let Some((_, s)) = fs.iter().find(|(k, _)| k == i).cloned() else {
                    return out("a type-valued field");
                };
                let t = format!("({} {xt})", sel_sym(self.e, *c, *i));
                if self.is_nat_tm(&self.e.g.cons[c.0 as usize].fields[*i].3.clone()) {
                    self.nat_fact(&t);
                }
                Ok((t, s))
            }
            Tm::Let(_, _, _, v, b) => {
                // Substituted rather than `let`-bound, so terms collected inside
                // (postconditions of calls) stay closed.
                let (vt, vs) = self.term(env, v)?;
                let mut env2 = env.to_vec();
                env2.push(Ent::Term(vt, vs));
                self.term(&env2, b)
            }
            Tm::App(..) | Tm::Def(_) | Tm::Con(_) => self.app(env, t),
            Tm::ConApp(c, args) => {
                let args: Vec<Tm> = args.clone();
                self.con_app(env, *c, &args)
            }
            Tm::PrimApp(p, args) => self.prim(env, p, args),
            Tm::Case(s, c) => self.case(env, s, c),
            Tm::Lam(..) => out("a lambda"),
            Tm::Error => out("code with a type error"),
            _ => out("a type used as a value"),
        }
    }

    fn sort_env(&self, id: TyId, sargs: &[Sort]) -> Vec<Ent> {
        let params = &self.e.g.tys[id.0 as usize].params;
        let mut k = 0;
        params
            .iter()
            .map(|(_, t)| {
                if self.is_type(t) {
                    k += 1;
                    Ent::Ty(sargs.get(k - 1).cloned().unwrap_or(Sort::Int))
                } else {
                    Ent::Opaque("value parameter".into())
                }
            })
            .collect()
    }

    fn con_app(&mut self, env: &[Ent], c: ConId, args: &[Tm]) -> Tx<(String, Sort)> {
        let wk = self.wk().clone();
        if Some(c) == wk.true_con {
            return Ok(("true".into(), Sort::Bool));
        }
        if Some(c) == wk.false_con {
            return Ok(("false".into(), Sort::Bool));
        }
        let ci = self.e.g.cons[c.0 as usize].fields.clone();
        let id = self.e.g.cons[c.0 as usize].ty;
        let np = self.e.g.arity_ty(id);
        if args.len() < np + ci.len() {
            return out("a partially applied constructor");
        }
        let sort = {
            let ptys: Vec<Tm> = args[..np].to_vec();
            self.ty_sort(env, id, &ptys)?
        };
        let Sort::Data(_, sargs) = &sort else { return out("a constructor of an abstract type") };
        let fs = self.con_fields(c, &self.sort_env(id, sargs))?;
        let mut ts = Vec::new();
        for (k, _) in &fs {
            let (t, _) = self.term(env, &args[np + k])?;
            ts.push(t);
        }
        let head = format!("(as {} {})", con_sym(self.e, c), sort.render(self.e));
        let t = if ts.is_empty() { head } else { format!("({head} {})", ts.join(" ")) };
        Ok((t, sort))
    }

    fn app(&mut self, env: &[Ent], t: &Tm) -> Tx<(String, Sort)> {
        let mut args: Vec<(Tm, Mult)> = Vec::new();
        let mut h = t;
        while let Tm::App(f, a, _, m) = h {
            args.push(((**a).clone(), *m));
            h = f;
        }
        args.reverse();
        match h {
            Tm::Con(c) => {
                let a: Vec<Tm> = args.into_iter().map(|x| x.0).collect();
                self.con_app(env, *c, &a)
            }
            Tm::Def(d) => self.def_app(env, *d, &args),
            Tm::Var(i) => match self.resolve(env, *i)? {
                Ent::Fun(name, sorts, r) => {
                    let mut ts = Vec::new();
                    for (a, m) in &args {
                        if *m != Mult::Zero {
                            ts.push(self.term(env, a)?.0);
                        }
                    }
                    if ts.len() != sorts.len() {
                        return out("a partially applied function");
                    }
                    let app = format!("({name} {})", ts.join(" "));
                    if !self.in_def && self.post_seen.insert(app.clone()) {
                        self.fun_post_facts(env, &name, &args, &app, &r);
                    }
                    Ok((app, r))
                }
                Ent::Known(k) => {
                    let f = self.known.get(&k).cloned().ok_or_else(|| Outside("an unknown function".into()))?;
                    self.apply_known(env, &f, &args)
                }
                _ => out("an application of a non-function"),
            },
            Tm::Lam(..) => self.apply_known(env, h, &args),
            Tm::Meta(m) if self.e.g.meta(*m).is_some() => {
                let z = self.zonk(env.len(), t);
                if has_meta(&z) {
                    return out("an unsolved unknown");
                }
                self.term(env, &z)
            }
            _ => out("an unsupported application"),
        }
    }

    /// Should `d`'s definition be visible to the solver (D12)?
    fn reflected(&self, d: DefId) -> bool {
        let info = &self.e.g.defs[d.0 as usize];
        // `opaque` covers `partial` functions and builtins.
        info.body.is_some() && !info.opaque && (*info.module == *self.user || self.e.transparent.contains(&d))
    }

    fn def_app(&mut self, env: &[Ent], d: DefId, args: &[(Tm, Mult)]) -> Tx<(String, Sort)> {
        let info = &self.e.g.defs[d.0 as usize];
        let qualified = format!("{}.{}", info.module, info.name);
        let ty = info.ty.clone();
        // Walk the binders: type arguments pick the instance, values are arguments.
        let mut tys = Vec::new();
        let mut funs: Vec<String> = Vec::new();
        let mut vals = Vec::new();
        let mut post_env = Vec::new();
        let mut inner: Vec<Ent> = Vec::new();
        let mut t = ty;
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = t.clone() {
            let Some((arg, _)) = args.get(k) else { return out(format!("a partial application of `{}`", info.name)) };
            if self.is_type(&a) {
                let s = self.sort_of(env, arg)?;
                tys.push(s.clone());
                inner.push(Ent::Ty(s.clone()));
                post_env.push(Ent::Ty(s));
            } else {
                if matches!(self.zonk(inner.len(), &a), Tm::Pi(..)) {
                    // A known function argument picks a specialized instance.
                    let Some(key) = self.known_fun(env, arg) else {
                        let what = if matches!(self.zonk(env.len(), arg), Tm::Lam(..)) {
                            "a lambda that uses local variables"
                        } else {
                            "a function value"
                        };
                        return out(format!("`{}` applied to {what} (only named functions and lambdas without free variables are seen through)", info.name));
                    };
                    funs.push(key.clone());
                    inner.push(Ent::Known(key.clone()));
                    post_env.push(Ent::Known(key));
                    t = (*b).clone();
                    k += 1;
                    continue;
                }
                let ps = self.sort_of(&inner, &a)?;
                let (at, _) = self.term(env, arg)?;
                vals.push(at.clone());
                inner.push(Ent::Term(at.clone(), ps.clone()));
                post_env.push(Ent::Term(at, ps));
            }
            t = (*b).clone();
            k += 1;
        }
        if k < args.len() {
            return out("a function returning a function");
        }
        let rs = self.sort_of(&inner, &t)?;
        // Builtins with a meaning in the solver.
        match qualified.as_str() {
            "std.bag.of" => {
                self.ensure_bag_of()?;
                return Ok((format!("(|bag.of| {})", vals.join(" ")), Sort::Bag));
            }
            "std.bag.count" => return Ok((format!("(select {} {})", vals[1], vals[0]), Sort::Int)),
            "std.bag.sum" => return Ok((format!("((_ map (+ (Int Int) Int)) {} {})", vals[0], vals[1]), Sort::Bag)),
            // A string is already its UTF-8 bytes.
            "std.utf8.encode" | "std.string.bytes" => return Ok((vals[0].clone(), Sort::Bytes)),
            // `word` occurs in `src` at `i` (the Rust primitive, exactly).
            "std.bytes.matches_at" => {
                let (src, i, w) = (&vals[0], &vals[1], &vals[2]);
                return Ok((
                    format!("(and (<= (+ {i} (seq.len {w})) (seq.len {src})) (= (seq.extract {src} {i} (seq.len {w})) {w}))"),
                    Sort::Bool,
                ));
            }
            _ => {}
        }
        let inst = Inst { def: d, tys: tys.clone(), funs: funs.clone() };
        let name = self.inst_name(&inst);
        if !self.insts.contains_key(&inst) && !self.funs.contains_key(&name) {
            if self.reflected(d) {
                self.insts.insert(inst.clone(), None);
                self.inst_queue.push(inst);
            } else {
                let mut arg_sorts = Vec::new();
                for e in &post_env {
                    if let Ent::Term(_, s) = e {
                        arg_sorts.push(s.render(self.e));
                    }
                }
                self.funs.insert(name.clone(), format!("(declare-fun {name} ({}) {})", arg_sorts.join(" "), rs.render(self.e)));
                if self.is_nat_tm(&t) {
                    self.nat_axiom(&name, &arg_sorts);
                }
            }
        }
        let app = if vals.is_empty() { name } else { format!("({name} {})", vals.join(" ")) };
        if !self.in_def {
            // At a call on program values the result is a `Nat` where the
            // callee's precondition holds (outside it, a reflected body such
            // as `n - 1` can be negative).
            let nat = self.is_nat_tm(&t);
            let spec = self.e.specs.get(&d);
            let has_pre = spec.is_some_and(|s| s.preds.iter().any(|p| !p.is_post));
            let has_post = spec.is_some_and(|s| s.preds.iter().any(|p| p.is_post));
            if nat && !has_pre {
                let a = app.clone();
                self.nat_fact(&a);
            }
            if (has_post || (nat && has_pre)) && self.post_seen.insert(app.clone()) {
                post_env.push(Ent::Term(app.clone(), rs.clone()));
                self.posts.push(PostUse { def: d, env: post_env, nat: nat && has_pre });
            }
        }
        Ok((app, rs))
    }

    fn ensure_bag_of(&mut self) -> Tx<()> {
        if self.funs.contains_key("|bag.of|") {
            return Ok(());
        }
        let wk = self.wk().clone();
        let (Some(list), Some(nil), Some(cons)) = (wk.list, wk.nil, wk.cons) else { return out("no lists") };
        self.ty_sort(&[], list, &[Tm::TyCon(wk.int.ok_or_else(|| Outside("no Int".into()))?)])?;
        let _ = nil;
        let def = format!(
            "(define-fun-rec |bag.of| ((xs ({l} Int))) (Array Int Int) (ite ({c} xs) (let ((b (|bag.of| ({t} xs))) (h ({hd} xs))) (store b h (+ (select b h) 1))) ((as const (Array Int Int)) 0)))",
            l = ty_sym(self.e, list),
            c = tester(self.e, cons),
            t = sel_sym(self.e, cons, 1),
            hd = sel_sym(self.e, cons, 0),
        );
        self.funs.insert("|bag.of|".into(), def);
        Ok(())
    }

    fn prim(&mut self, env: &[Ent], p: &Prim, args: &[Tm]) -> Tx<(String, Sort)> {
        let mut ts = Vec::new();
        let n = if *p == Prim::Sub { 2 } else { args.len() };
        for a in &args[..n.min(args.len())] {
            ts.push(self.term(env, a)?);
        }
        let bin = |op: &str, ts: &[(String, Sort)], s: Sort| Ok((format!("({op} {} {})", ts[0].0, ts[1].0), s));
        match p {
            Prim::Add => bin("+", &ts, Sort::Int),
            Prim::Sub => bin("-", &ts, Sort::Int),
            Prim::Mul => bin("*", &ts, Sort::Int),
            Prim::Div => bin("div", &ts, Sort::Int),
            Prim::Rem => bin("mod", &ts, Sort::Int),
            Prim::Neg => Ok((format!("(- {})", ts[0].0), Sort::Int)),
            Prim::Lt => bin("<", &ts, Sort::Bool),
            Prim::Le => bin("<=", &ts, Sort::Bool),
            Prim::Gt => bin(">", &ts, Sort::Bool),
            Prim::Ge => bin(">=", &ts, Sort::Bool),
            Prim::Eq => bin("=", &ts, Sort::Bool),
            Prim::Ne => Ok((format!("(not (= {} {}))", ts[0].0, ts[1].0), Sort::Bool)),
            Prim::Concat => match &ts[0].1 {
                Sort::Str => bin("seq.++", &ts, Sort::Str),
                Sort::Bytes => bin("seq.++", &ts, Sort::Bytes),
                s @ Sort::Data(..) => {
                    let s = s.clone();
                    let f = self.list_fun("append", &s, 2, s.clone())?;
                    Ok((format!("({f} {} {})", ts[0].0, ts[1].0), s))
                }
                _ => out("`++` on this type"),
            },
            Prim::Len => match &ts[0].1 {
                Sort::Bytes => Ok((format!("(seq.len {})", ts[0].0), Sort::Int)),
                Sort::Str => Ok((format!("(seq.len {})", ts[0].0), Sort::Int)),
                s @ Sort::Data(..) => {
                    let s = s.clone();
                    let f = self.list_fun("len", &s, 1, Sort::Int)?;
                    let ls = s.render(self.e);
                    self.nat_axiom(&f, &[ls]);
                    let t = format!("({f} {})", ts[0].0);
                    self.nat_fact(&t);
                    Ok((t, Sort::Int))
                }
                _ => out("`len` on this type"),
            },
            Prim::Index => {
                let t = format!("(seq.nth {} {})", ts[0].0, ts[1].0);
                // Every element of `Bytes` is a `U8`.
                if !self.in_def && self.nat_seen.insert(t.clone()) {
                    self.asserts.push(format!("(and (>= {t} 0) (< {t} 256))"));
                }
                Ok((t, Sort::Int))
            }
            Prim::Format => {
                let s = ts[0].1.render(self.e);
                let f = sym(&format!("format<{s}>"));
                self.funs.insert(f.clone(), format!("(declare-fun {f} ({s}) (Seq Int))"));
                Ok((format!("({f} {})", ts[0].0), Sort::Str))
            }
            Prim::Par => Ok(ts[0].clone()),
            Prim::When | Prim::Fork | Prim::Join => out("a concurrency form (`when`, `fork`, `join`)"),
            Prim::Builtin(n) => out(format!("the builtin `{n}`")),
        }
    }

    /// `++` and `len` on lists, as recursive functions.
    fn list_fun(&mut self, what: &str, list: &Sort, _arity: usize, _res: Sort) -> Tx<String> {
        let wk = self.wk().clone();
        let (Some(cons), Some(nil)) = (wk.cons, wk.nil) else { return out("no lists") };
        let ls = list.render(self.e);
        let name = sym(&format!("list.{what}<{ls}>"));
        if self.funs.contains_key(&name) {
            return Ok(name);
        }
        let is_cons = tester(self.e, cons);
        let hd = sel_sym(self.e, cons, 0);
        let tl = sel_sym(self.e, cons, 1);
        let def = match what {
            "len" => format!("(define-fun-rec {name} ((xs {ls})) Int (ite ({is_cons} xs) (+ 1 ({name} ({tl} xs))) 0))"),
            _ => format!(
                "(define-fun-rec {name} ((xs {ls}) (ys {ls})) {ls} (ite ({is_cons} xs) ((as {c} {ls}) ({hd} xs) ({name} ({tl} xs) ys)) ys))",
                c = con_sym(self.e, cons)
            ),
        };
        let _ = nil;
        self.funs.insert(name.clone(), def);
        Ok(name)
    }

    fn case(&mut self, env: &[Ent], s: &Tm, c: &CaseTm) -> Tx<(String, Sort)> {
        let (st, ss) = self.term(env, s)?;
        let x = st.clone();
        let mut arms: Vec<(Option<String>, String, Sort)> = Vec::new();
        match &ss {
            Sort::Bool => {
                for (con, _, body) in &c.branches {
                    if matches!(body, Tm::Error) {
                        continue;
                    }
                    let (bt, bs) = self.term(env, body)?;
                    let cond = if Some(*con) == self.wk().true_con { x.clone() } else { format!("(not {x})") };
                    arms.push((Some(cond), bt, bs));
                }
            }
            Sort::Data(id, sargs) => {
                let senv = self.sort_env(*id, sargs);
                for (con, n, body) in &c.branches {
                    if matches!(body, Tm::Error) {
                        continue;
                    }
                    let fs = self.con_fields(*con, &senv)?;
                    let mut env2 = env.to_vec();
                    for k in 0..*n {
                        match fs.iter().find(|(i, _)| *i == k) {
                            Some((_, fsort)) => env2.push(Ent::Term(format!("({} {x})", sel_sym(self.e, *con, k)), fsort.clone())),
                            None => env2.push(Ent::Ty(Sort::Unin("field".into(), vec![]))),
                        }
                    }
                    let (bt, bs) = self.term(&env2, body)?;
                    arms.push((Some(format!("({} {x})", tester(self.e, *con))), bt, bs));
                }
            }
            Sort::Tuple(_) => {
                // A tuple has one constructor.
                if let Some((_, _, body)) = c.branches.first() {
                    let (bt, bs) = self.term(env, body)?;
                    arms.push((None, bt, bs));
                }
            }
            _ => {}
        }
        for (l, body) in &c.lits {
            if matches!(body, Tm::Error) {
                continue;
            }
            let lt = match l {
                Lit::Num(n) => if *n < 0 { format!("(- {})", -n) } else { n.to_string() },
                Lit::Str(s) => smt_bytes(s.as_bytes()),
                Lit::Bytes(b) => smt_bytes(b),
            };
            let (bt, bs) = self.term(env, body)?;
            arms.push((Some(format!("(= {x} {lt})")), bt, bs));
        }
        if let Some(d) = c.default.as_ref().filter(|d| !matches!(d, Tm::Error)) {
            let (bt, bs) = self.term(env, d)?;
            arms.push((None, bt, bs));
        }
        let Some((_, last, sort)) = arms.pop() else { return out("a `match` with no reachable arm") };
        let mut acc = last;
        while let Some((cond, bt, _)) = arms.pop() {
            acc = match cond {
                Some(c) => format!("(ite {c} {bt} {acc})"),
                None => bt,
            };
        }
        Ok((acc, sort))
    }

    // ── reflected definitions and postconditions ────────────────────────────

    /// The definitions: all reflected; all uninterpreted; and the parts to
    /// reflect some only (`focus`).
    fn define_instances(&mut self) -> (Vec<String>, Vec<String>, Focus) {
        while let Some(inst) = self.inst_queue.pop() {
            let r = self.define_shared(&inst);
            // A `Nat` result is non-negative, for every argument.
            let mut ty = self.e.g.defs[inst.def.0 as usize].ty.clone();
            while let Tm::Pi(_, _, _, _, b) = ty {
                ty = (*b).clone();
            }
            // Z3 applies the definition to values no program can build
            // (`Option Nat` is `Option Int` to it; invariants and
            // preconditions aren't in sorts), where a `Nat` body can be
            // negative. So "the result is >= 0 for every argument" is stated
            // only when it holds for every solver value (`nonneg_fn`).
            if self.is_nat_tm(&ty) && self.nonneg_fn(inst.def, &mut Vec::new()) {
                if let Ok((_, params, _)) = self.inst_sig(&inst) {
                    let name = self.inst_name(&inst);
                    let sorts: Vec<String> = params.iter().map(|(_, s)| s.render(self.e)).collect();
                    self.nat_axiom(&name, &sorts);
                }
            }
            self.insts.insert(inst, r.ok());
        }
        let mut heads = Vec::new();
        let mut bodies = Vec::new();
        let mut decls = Vec::new();
        let mut opaque = Vec::new();
        let mut group = Vec::new();
        let all: Vec<(Inst, Option<Defn>)> = self.insts.iter().map(|(a, b)| (a.clone(), b.clone())).collect();
        for (inst, def) in &all {
            match def {
                Some((name, head, body)) => {
                    heads.push(head.clone());
                    bodies.push(body.clone());
                    let d = self.uninterp_decl(inst);
                    if let Some(d) = &d {
                        opaque.push(d.clone());
                    }
                    group.push((name.clone(), head.clone(), body.clone(), d));
                }
                None => {
                    // Not translatable: uninterpreted.
                    if let Some(d) = self.uninterp_decl(inst) {
                        decls.push(d);
                    }
                }
            }
        }
        let reflected = !heads.is_empty();
        if reflected {
            decls.push(format!("(define-funs-rec ({}) ({}))", heads.join(" "), bodies.join(" ")));
        }
        // The uninterpreted variant shares the rest (`decls` minus the group).
        let mut only = decls.clone();
        if reflected {
            only.pop();
        }
        let focus = Focus { others: only.clone(), group };
        if reflected {
            only.extend(opaque);
        }
        (decls, only, focus)
    }

    fn inst_name(&self, inst: &Inst) -> String {
        let info = &self.e.g.defs[inst.def.0 as usize];
        let mut q = format!("{}.{}", info.module, info.name);
        if !inst.tys.is_empty() {
            q += &format!("<{}>", inst.tys.iter().map(|s| s.render(self.e)).collect::<Vec<_>>().join(","));
        }
        if !inst.funs.is_empty() {
            q += &format!("[{}]", inst.funs.join(","));
        }
        sym(&q)
    }

    /// If `arg` (under `env`) is a known function value, its key.
    fn known_fun(&mut self, env: &[Ent], arg: &Tm) -> Option<String> {
        let arg = self.zonk(env.len(), arg);
        if let Tm::Var(i) = &arg {
            return match self.resolve(env, *i).ok()? {
                Ent::Known(k) => Some(k),
                _ => None,
            };
        }
        if !closed(&arg, 0) {
            return None;
        }
        let mut h = &arg;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        let key = match h {
            Tm::Def(d) if matches!(arg, Tm::Def(_)) => {
                let info = &self.e.g.defs[d.0 as usize];
                format!("{}.{}", info.module, info.name)
            }
            _ => {
                use std::hash::{Hash, Hasher};
                let mut hs = std::collections::hash_map::DefaultHasher::new();
                // Binder names don't matter: `\x -> …` written twice is one function.
                let mut text = format!("{arg:?}");
                for binder in ["Lam(\"", "Pi(\"", "Let(\""] {
                    let mut out_ = String::new();
                    let mut rest = text.as_str();
                    while let Some(k) = rest.find(binder) {
                        out_ += &rest[..k + binder.len()];
                        rest = &rest[k + binder.len()..];
                        if let Some(e) = rest.find('"') {
                            rest = &rest[e..];
                        }
                    }
                    out_ += rest;
                    text = out_;
                }
                text.hash(&mut hs);
                if std::env::var_os("CHECKERS_KNOWN_DUMP").is_some() {
                    eprintln!("KNOWN {:08x} {arg:?}", hs.clone().finish() as u32);
                }
                format!("fn#{:08x}", hs.finish() as u32)
            }
        };
        self.known.insert(key.clone(), arg);
        Some(key)
    }

    /// Apply a closed function term to arguments under `env`.
    fn apply_known(&mut self, env: &[Ent], f: &Tm, args: &[(Tm, Mult)]) -> Tx<(String, Sort)> {
        match f {
            Tm::Lam(..) => {
                // The body sees only its parameters (the lambda is closed).
                let mut inner = Vec::new();
                let mut body = f;
                for (a, _) in args {
                    let Tm::Lam(_, _, _, b) = body else { return out("a lambda returning a function") };
                    let (at, s) = self.term(env, a)?;
                    inner.push(Ent::Term(at, s));
                    body = b;
                }
                if matches!(body, Tm::Lam(..)) {
                    return out("a partially applied lambda");
                }
                let body = body.clone();
                self.term(&inner, &body)
            }
            _ => {
                // Re-express the arguments as variables of a fresh environment.
                let mut inner = Vec::new();
                let mut tms = Vec::new();
                let n = args.len();
                for (k, (a, m)) in args.iter().enumerate() {
                    let ent = match self.known_fun(env, a) {
                        Some(key) => Ent::Known(key),
                        None => match self.term(env, a) {
                            Ok((t, s)) => Ent::Term(t, s),
                            Err(e) => match self.sort_of(env, a) {
                                Ok(s) => Ent::Ty(s),
                                Err(_) => return Err(e),
                            },
                        },
                    };
                    inner.push(ent);
                    tms.push((Tm::Var(n - 1 - k), *m));
                }
                let mut app = f.clone();
                for (t, m) in tms {
                    app = Tm::App(Rc::new(app), Rc::new(t), crate::core::Icit::Expl, m);
                }
                self.term(&inner, &app)
            }
        }
    }

    fn inst_sig(&mut self, inst: &Inst) -> Tx<InstSig> {
        let ty = self.e.g.defs[inst.def.0 as usize].ty.clone();
        let mut env = Vec::new();
        let mut params = Vec::new();
        let mut t = ty;
        let mut tk = 0;
        let mut fk = 0;
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = t.clone() {
            if self.is_type(&a) {
                env.push(Ent::Ty(inst.tys.get(tk).cloned().unwrap_or(Sort::Int)));
                tk += 1;
            } else if matches!(self.zonk(env.len(), &a), Tm::Pi(..)) {
                let key = inst.funs.get(fk).cloned().ok_or_else(|| Outside("a function parameter".into()))?;
                env.push(Ent::Known(key));
                fk += 1;
            } else {
                let s = self.sort_of(&env, &a)?;
                let n = format!("p{k}");
                params.push((n.clone(), s.clone()));
                env.push(Ent::Term(n, s));
            }
            t = (*b).clone();
            k += 1;
        }
        let r = self.sort_of(&env, &t)?;
        Ok((env, params, r))
    }

    fn uninterp_decl(&mut self, inst: &Inst) -> Option<String> {
        let name = self.inst_name(inst);
        let (_, params, r) = self.inst_sig(inst).ok()?;
        Some(format!(
            "(declare-fun {name} ({}) {})",
            params.iter().map(|(_, s)| s.render(self.e)).collect::<Vec<_>>().join(" "),
            r.render(self.e)
        ))
    }

    fn define(&mut self, inst: &Inst) -> Tx<Defn> {
        let name = self.inst_name(inst);
        let (env, params, r) = self.inst_sig(inst)?;
        let mut body = self.e.g.defs[inst.def.0 as usize].body.clone().ok_or_else(|| Outside("no body".into()))?;
        for _ in 0..env.len() {
            match body {
                Tm::Lam(_, _, _, b) => body = (*b).clone(),
                _ => return out("a body that is not a function"),
            }
        }
        let saved = self.in_def;
        self.in_def = true;
        let r_body = self.term(&env, &body);
        self.in_def = saved;
        let (bt, _) = r_body?;
        let head = format!(
            "({name} ({}) {})",
            params.iter().map(|(n, s)| format!("({n} {})", s.render(self.e))).collect::<Vec<_>>().join(" "),
            r.render(self.e)
        );
        Ok((name, head, bt))
    }

    fn assume_posts(&mut self) {
        let mut rounds = 0;
        while !self.posts.is_empty() && rounds < 3 {
            rounds += 1;
            let posts = std::mem::take(&mut self.posts);
            for p in posts {
                let Some(spec) = self.e.specs.get(&p.def).cloned() else { continue };
                // The postcondition holds where the precondition does.
                let mut pres = Vec::new();
                let mut ok = true;
                for pred in spec.preds.iter().filter(|x| !x.is_post) {
                    match self.term(&p.env, &pred.tm) {
                        Ok((t, _)) => pres.push(t),
                        Err(_) => ok = false,
                    }
                }
                if !ok {
                    continue;
                }
                let mut goals = Vec::new();
                if p.nat {
                    if let Some(Ent::Term(r, _)) = p.env.last() {
                        goals.push(format!("(>= {r} 0)"));
                    }
                }
                for pred in spec.preds.iter().filter(|x| x.is_post) {
                    if let Ok((t, _)) = self.term(&p.env, &pred.tm) {
                        goals.push(t);
                    }
                }
                for t in goals {
                    self.asserts.push(match pres.len() {
                        0 => t,
                        1 => format!("(=> {} {t})", pres[0]),
                        _ => format!("(=> (and {}) {t})", pres.join(" ")),
                    });
                }
            }
        }
    }

    /// The full query for an obligation: facts, and the negated goal.
    pub fn query(mut self, ob: &Obligation) -> Tx<Query> {
        self.ctx = vec![None; ob.ctx.len()];
        self.ctx_src = ob.ctx.clone();
        let lvl = ob.ctx.len();
        let goal_tm = quote(&self.e.g, lvl, &ob.goal);
        let (goal, gs) = self.term_ctx(lvl, &goal_tm)?;
        if gs != Sort::Bool {
            return out("a goal that is not a `Bool`");
        }
        let mut facts = Vec::new();
        let mut dropped = Vec::new();
        for f in &ob.facts {
            let tm = quote(&self.e.g, lvl, f);
            // A fact the solver can't see is simply not assumed.
            match self.term_ctx(lvl, &tm) {
                Ok((t, Sort::Bool)) => facts.push(t),
                Ok(_) => {}
                Err(why) => {
                    if !dropped.contains(&why.0) {
                        dropped.push(why.0);
                    }
                }
            }
        }
        self.assume_posts();
        let (defs, opaque_defs, focus) = self.define_instances();
        let reflected = defs.len() != opaque_defs.len() || defs.iter().zip(&opaque_defs).any(|(a, b)| a != b);
        // Definitions may mention new datatypes; postconditions inside them are not assumed.
        let sorts = self.sort_decls()?;
        let mut text = String::new();
        text += &format!(
            "(set-option :produce-models true)\n(set-option :rlimit {})\n(set-option :timeout {})\n(set-logic ALL)\n",
            super::RLIMIT,
            super::SAFETY_MS
        );
        for s in sorts {
            text += &s;
            text += "\n";
        }
        for f in self.funs.values() {
            if f.starts_with("(declare-fun") {
                text += f;
                text += "\n";
            }
        }
        for f in self.funs.values() {
            if f.starts_with("(define-fun-rec") {
                text += f;
                text += "\n";
            }
        }
        let defs_at = text.len();
        for d in &defs {
            text += d;
            text += "\n";
        }
        let defs_end = text.len();
        let mut axioms = String::new();
        for a in self.axioms.values() {
            axioms += &format!("(assert {a})\n");
        }
        let split = text.len();
        text += &axioms;
        for c in &self.consts {
            text += c;
            text += "\n";
        }
        for a in self.asserts.iter().chain(facts.iter()) {
            text += &format!("(assert {a})\n");
        }
        text += &format!("(assert (not {goal}))\n(check-sat)\n");
        if !self.shown.is_empty() {
            text += &format!("(get-value ({}))\n", self.shown.iter().map(|s| s.0.clone()).collect::<Vec<_>>().join(" "));
        }
        let without_axioms = (!axioms.is_empty()).then(|| format!("{}{}", &text[..split], &text[split + axioms.len()..]));
        let facts_only = reflected.then(|| {
            let decls: String = opaque_defs.iter().map(|d| format!("{d}\n")).collect();
            format!("{}{decls}{}", &text[..defs_at], &text[defs_end..])
        });
        let focused = focus
            .for_goal(&goal)
            .map(|d| format!("{}{d}{}{}", &text[..defs_at], &text[defs_end..split], &text[split + axioms.len()..]));
        Ok(Query { text, without_axioms, facts_only, focused, dropped, shown: self.shown, string_vars: self.string_vars })
    }
}

/// No variable of `t` reaches outside `depth` enclosing binders.
fn closed(t: &Tm, depth: usize) -> bool {
    match t {
        Tm::Var(i) => *i < depth,
        Tm::Pi(_, _, _, a, b) => closed(a, depth) && closed(b, depth + 1),
        Tm::Lam(_, _, _, b) => closed(b, depth + 1),
        Tm::App(a, b, _, _) => closed(a, depth) && closed(b, depth),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().all(|a| closed(a, depth))
        }
        Tm::Proj(a, _) | Tm::Field(a, _, _) => closed(a, depth),
        Tm::Let(_, _, a, b, c) => closed(a, depth) && closed(b, depth) && closed(c, depth + 1),
        Tm::Case(sc, c) => {
            closed(sc, depth)
                && c.branches.iter().all(|(_, n, b)| closed(b, depth + n))
                && c.lits.iter().all(|(_, b)| closed(b, depth))
                && c.default.as_ref().is_none_or(|b| closed(b, depth))
        }
        Tm::Meta(_) | Tm::Error => false,
        _ => true,
    }
}

fn max_var(t: &Tm) -> Option<usize> {
    let m = |a: Option<usize>, b: Option<usize>| a.max(b);
    match t {
        Tm::Var(i) => Some(*i),
        Tm::App(f, a, ..) => m(max_var(f), max_var(a)),
        _ => None,
    }
}

fn has_meta(t: &Tm) -> bool {
    match t {
        Tm::Meta(_) => true,
        Tm::App(f, a, ..) => has_meta(f) || has_meta(a),
        Tm::Pi(_, _, _, a, b) => has_meta(a) || has_meta(b),
        Tm::Lam(_, _, _, b) => has_meta(b),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(has_meta),
        Tm::Proj(x, _) | Tm::Field(x, _, _) => has_meta(x),
        Tm::Let(_, _, a, b, c) => has_meta(a) || has_meta(b) || has_meta(c),
        _ => false,
    }
}


fn smt_bytes(b: &[u8]) -> String {
    if b.is_empty() {
        return "(as seq.empty (Seq Int))".into();
    }
    let units: Vec<String> = b.iter().map(|x| format!("(seq.unit {x})")).collect();
    if units.len() == 1 {
        units[0].clone()
    } else {
        format!("(seq.++ {})", units.join(" "))
    }
}

/// Is a value `Nat`-typed? (for `only_if_nat` obligations)
pub fn is_nat(e: &Elab, ty: &Val) -> bool {
    matches!(force(&e.g, ty.clone()), Val::TyCon(t, _) if Some(t) == e.g.well_known.nat)
}
