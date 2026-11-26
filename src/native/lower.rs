//! Closure conversion (D72, §14): erased code (`native::ir::Ir`,
//! curried and de Bruijn-indexed) becomes first-order functions over
//! numbered variables. Every lambda becomes a function taking its closure
//! (the environment) and its arguments; saturated calls of known functions
//! are direct. Arguments of primitives and builtins are atoms, so that the
//! reference-counting pass can treat them as borrowed.

use crate::core::{ConId, DefId, Globals, Mult, Tm};
use crate::native::ir::{Compiler, Ir, Lit as RtLit, Op};
use crate::range::Range;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

pub type V = u32;

#[derive(Clone)]
pub enum E {
    Var(V),
    Int(i64),
    /// A number too big for a word: its decimal digits.
    BigLit(String),
    Str(Arc<str>),
    Bytes(Arc<[u8]>),
    /// A value made only of literals, constructors and tuples: static data,
    /// built when the program is compiled rather than each time it runs.
    Static(Arc<Static>),
    Erased,
    Unit,
    /// The value of a definition: its global closure, or a constant.
    Global(u32),
    /// A constructor used as a function: its global closure.
    ConFn(u32),
    Let(V, Box<E>, Box<E>),
    /// A saturated call of a known function.
    Call { f: u32, args: Vec<E>, tail: bool },
    /// Apply a function value.
    Apply { f: Box<E>, args: Vec<E>, tail: bool },
    MkClo { f: u32, captured: Vec<V> },
    /// `reuse`: memory of a value being dropped, to build in place (D74).
    Con { con: u32, fields: Vec<E>, reuse: Option<V> },
    Tuple(Vec<E>),
    /// An operation that borrows its (atomic) arguments; `drops` are
    /// dropped after it (filled in by the reference-counting pass).
    Borrow { op: BOp, args: Vec<E>, drops: Vec<V> },
    Case { scrut: V, arms: Vec<Arm>, lits: Vec<(E, E)>, default: Option<Box<E>> },
    /// `par`: closures taking `()`.
    Par(Vec<E>),
    Fail(&'static str),
    // Inserted by the reference-counting pass.
    Dup(V, Box<E>),
    Drop(V, Box<E>),
    /// `DropReuse(x, token, n, e)`: drop `x`, a constructor value with `n`
    /// fields; if it was the only reference, its memory becomes `token`
    /// (else `token` is 0).
    DropReuse(V, V, usize, Box<E>),
    /// Code of another definition (`Ir::At`): its runtime errors name that
    /// definition.
    At(u32, Box<E>),
    // Inserted by `unbox` (a value's parts returned in registers, §14).
    /// Several values at once, each owned: the parts of a constructor
    /// value that is never built. Only where the code's value goes to a
    /// `LetMulti` or is the result of a function returning several words.
    Multi(Vec<E>),
    /// `LetMulti(xs, a, b)`: bind the values `a` gives (`Multi`, or a call
    /// of a function returning several words) to `xs`, then `b`.
    LetMulti(Vec<V>, Box<E>, Box<E>),
}

/// A value known when the program is compiled (`E::Static`).
pub enum Static {
    /// An integer, a constructor without fields, `()` or an erased value.
    Word(u64),
    Str(Arc<str>),
    Bytes(Arc<[u8]>),
    Con(u32, Vec<Arc<Static>>),
    Tuple(Vec<Arc<Static>>),
}

impl Static {
    /// `e` as static data, if it is a literal or built from them.
    fn of(e: &E) -> Option<Arc<Static>> {
        use checkers_rt::word as w;
        Some(Arc::new(match e {
            E::Int(n) => Static::Word(w::mk_int(*n)),
            E::Str(s) => Static::Str(s.clone()),
            E::Bytes(b) => Static::Bytes(b.clone()),
            E::Erased => Static::Word(w::ERASED),
            E::Unit => Static::Word(w::UNIT),
            E::Con { con, fields, reuse: None } if fields.is_empty() => Static::Word(w::nullary(*con)),
            E::Static(x) => return Some(x.clone()),
            _ => return None,
        }))
    }

    /// A constructor or tuple whose fields are all static, as one value.
    fn fold(e: E) -> E {
        let fields = match &e {
            E::Con { fields, reuse: None, .. } | E::Tuple(fields) if !fields.is_empty() => fields,
            _ => return e,
        };
        let Some(xs) = fields.iter().map(Static::of).collect::<Option<Vec<_>>>() else { return e };
        E::Static(Arc::new(match e {
            E::Con { con, .. } => Static::Con(con, xs),
            _ => {
                // `(a, (b, c))` is `(a, b, c)` (D174).
                let mut xs = xs;
                if let Some(Static::Tuple(ys)) = xs.last().map(|l| &**l) {
                    if ys.len() >= 2 {
                        let ys = ys.clone();
                        xs.pop();
                        xs.extend(ys);
                    }
                }
                Static::Tuple(xs)
            }
        }))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BOp {
    Prim(Op, bool),
    /// A builtin: its runtime symbol.
    Builtin(&'static str),
    Field(usize),
    Proj(usize),
    /// A tuple's component `i` and the rest after it (D174).
    ProjRest(usize),
    /// `[cell, i, x]`: store `x` (one more reference) in field `i` (an
    /// integer word) of a new constructor cell whose field `i` is empty;
    /// `()`. Only the code `tailrec` writes fills a cell this way.
    SetField,
    /// `[x, pieces]`: `x ++ p1 ++ … ++ pk` for the list `pieces` of
    /// `[p1, …, pk]`, each element copied once (`ck_concat_all`). Only the
    /// code `tailrec` writes appends this way.
    ConcatAll,
}

#[derive(Clone)]
pub struct Arm {
    pub con: u32,
    /// The variables the arm binds for the constructor's fields (`None`:
    /// not used).
    pub fields: Vec<Option<V>>,
    pub body: E,
}

#[derive(Clone)]
pub enum FnKind {
    /// A definition's function: it ignores its environment.
    Global,
    /// A lambda: its closure holds `captured`.
    Lambda { captured: Vec<V> },
    /// A builtin used as a value: calls the runtime with the kept arguments.
    BuiltinWrap { sym: &'static str, keep: Vec<bool> },
    /// A constructor used as a function.
    ConWrap { con: u32, np: usize, erased: Vec<bool> },
    /// Computes a constant's value (once).
    Caf,
}

#[derive(Clone)]
pub struct Func {
    pub name: String,
    /// The definition this code belongs to (for runtime errors).
    pub owner: u32,
    pub kind: FnKind,
    pub params: Vec<V>,
    pub body: E,
    /// Variables are numbered from 0 to `nvars`.
    pub nvars: u32,
    /// How many words it returns: 1, or a value's parts (`unbox`).
    pub rets: usize,
    /// Constant bounds of variables, true wherever they are bound: its
    /// parameters' from its signature (`Globals::bounds`).
    pub bounds: HashMap<V, Range>,
}

/// How a definition is called.
#[derive(Clone)]
pub enum DefShape {
    /// A function of this many parameters: `Func` index.
    Fn { func: u32, arity: usize },
    /// A builtin: runtime symbol, kept-parameter mask, wrapper function.
    Builtin { sym: &'static str, keep: Vec<bool>, wrap: u32 },
    /// A constant computed on first use: `Func` index of its code.
    Caf { func: u32 },
    /// Not available at run time.
    Missing(String),
}

pub struct Program {
    /// Functions; those from `rc_done` on still need reference counting.
    pub funcs: Vec<Func>,
    pub rc_done: usize,
    /// Compiled code of each definition lowered so far.
    pub code: HashMap<u32, Arc<Ir>>,
    pub defs: HashMap<u32, DefShape>,
    /// Constructor wrapper functions, by constructor.
    pub con_wraps: HashMap<u32, u32>,
    /// All definition names (including staged ones), for error messages.
    pub names: Vec<String>,
    /// `main`, when the program has one.
    pub main: u32,
    /// The code computing the hand-written `Debug` instances' functions, a
    /// list in the order of `Globals::well_known.debug_insts` (#126).
    pub debug: Option<u32>,
    /// Which definitions are recursive, for `inline`.
    pub recursive: HashMap<u32, bool>,
    /// Each definition's code after `inline`, as far as computed.
    pub inlined: HashMap<u32, Arc<Ir>>,
    /// Definitions given a function and not lowered yet.
    pub wanted: Vec<u32>,
    /// Functions' copies specialized to known instances' dictionaries
    /// (`spec`), numbered after the definitions.
    pub specs: std::cell::RefCell<crate::native::spec::Specs>,
    /// Functions whose results are returned as their parts (`unbox`): the
    /// function returning them, and their layout.
    pub workers: HashMap<u32, (u32, crate::native::unbox::Shape)>,
    /// Functions' borrowed parameters (`rc::infer_borrowed`).
    pub borrowed: HashMap<u32, Vec<bool>>,
    /// Where a closure of a function with borrowed parameters enters: a
    /// function taking them owned, which calls it and drops them after.
    pub entries: HashMap<u32, u32>,
    /// The most words a function returns (`unbox`): what the machine the
    /// code is compiled for returns in registers. This machine's, unless
    /// set before reference counting.
    pub max_parts: usize,
}

/// Code with no definition (a `check`, a value staging computes).
pub const NO_OWNER: u32 = u32::MAX;

/// Adds to a `Program`.
pub struct Lowerer<'a, 'g> {
    g: &'g Globals,
    staged: Option<&'a crate::stage::Staged>,
    p: &'a mut Program,
    // Per function being lowered:
    next: u32,
    owner: u32,
}

/// The most parameters a native function takes: the runtime calls compiled
/// code through a table with one entry for each arity (`ck_invoke`).
pub const MAX_ARITY: usize = 64;

/// The arity of code: how many lambdas it starts with, up to `MAX_ARITY`.
/// Further lambdas stay in the body, so a wider function is curried: it
/// returns a closure that takes the next parameters.
fn lams(ir: &Ir) -> (usize, &Ir) {
    let mut n = 0;
    let mut b = ir;
    while let (true, Ir::Lam(_, x)) = (n < MAX_ARITY, b) {
        n += 1;
        b = x;
    }
    (n, b)
}

impl Program {
    pub fn new(g: &Globals, staged: Option<&crate::stage::Staged>) -> Program {
        let mut names: Vec<String> = g.defs.iter().map(|d| d.name.to_string()).collect();
        if let Some(s) = staged {
            names.extend(s.extra.iter().map(|e| e.0.clone()));
        }
        let base = names.len() as u32;
        Program {
            specs: std::cell::RefCell::new(crate::native::spec::Specs::new(base)),
            funcs: Vec::new(),
            rc_done: 0,
            code: HashMap::new(),
            defs: HashMap::new(),
            con_wraps: HashMap::new(),
            names,
            main: NO_OWNER,
            debug: None,
            recursive: HashMap::new(),
            inlined: HashMap::new(),
            wanted: Vec::new(),
            workers: HashMap::new(),
            borrowed: HashMap::new(),
            entries: HashMap::new(),
            max_parts: crate::native::host_return_words(),
        }
    }
}

/// How many type parameters function `d` takes before its other arguments.
pub fn type_params(g: &Globals, d: DefId) -> usize {
    let mut n = 0;
    let mut ty = &g.defs[d.0 as usize].ty;
    while let Tm::Pi(_, Mult::Zero, crate::core::Icit::Impl, _, b) = ty {
        n += 1;
        ty = b;
    }
    n
}

/// The hand-written `Debug` instances' functions (#126), as a closed term:
/// a list of them, each taking its type's parameters' words (#170), then
/// the value. `None` if the program has none.
pub fn debug_table(g: &Globals) -> Option<Tm> {
    use crate::core::Icit;
    use std::rc::Rc;
    let insts = &g.well_known.debug_insts;
    let (nil, cons) = (g.well_known.nil?, g.well_known.cons?);
    if insts.is_empty() {
        return None;
    }
    let erased = |f: Tm| Tm::App(Rc::new(f), Rc::new(Tm::Univ(0)), Icit::Impl, Mult::Zero);
    let mut list = erased(Tm::Con(nil));
    for (_, d) in insts.iter().rev() {
        // Its type parameters come from the runtime, which knows them from
        // the value's type's descriptor (#170).
        let f = Tm::Def(*d);
        let c = erased(Tm::Con(cons));
        list = Tm::App(Rc::new(Tm::App(Rc::new(c), Rc::new(f), Icit::Expl, Mult::Many)), Rc::new(list), Icit::Expl, Mult::Many);
    }
    Some(list)
}

/// The whole program reachable from `main`.
pub fn lower(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId) -> Program {
    let mut p = Program::new(g, staged);
    Lowerer::new(g, staged, &mut p).add_defs(&[main.0]);
    p.main = main.0;
    if let Some(ir) = show_table(g) {
        p.debug = Some(Lowerer::new(g, staged, &mut p).add_closed_ir(&ir));
    }
    p
}

impl<'a, 'g> Lowerer<'a, 'g> {
    pub fn new(g: &'g Globals, staged: Option<&'a crate::stage::Staged>, p: &'a mut Program) -> Self {
        Lowerer { g, staged, p, next: 0, owner: 0 }
    }

    /// Lower `roots` and every definition they reach that isn't lowered yet.
    pub fn add_defs(&mut self, roots: &[u32]) {
        let g = self.g;
        let staged = self.staged;
        let ndefs = g.defs.len() + staged.map_or(0, |s| s.extra.len());
        // Compile every new reachable definition.
        let mut referenced = BTreeSet::new();
        let mut todo: Vec<u32> = roots.to_vec();
        while let Some(d) = todo.pop() {
            if self.p.code.contains_key(&d) || self.p.defs.contains_key(&d) {
                continue;
            }
            // A specialized copy (`spec`): its body, compiled as code of
            // the function it copies.
            let copy = self.p.specs.borrow().copy(d).map(|c| (c.of, c.body.clone(), c.depth));
            let (owner, body, depth) = match copy {
                Some(c) => (c.0, Some(c.1), c.2),
                None if (d as usize) < ndefs => (DefId(d), crate::native::ir::body_of(g, staged, DefId(d)), 0),
                None => continue,
            };
            let Some(body) = body else {
                referenced.insert(d);
                continue;
            };
            let spec = crate::native::spec::SpecCx { table: &self.p.specs, staged, depth };
            let c = Compiler { g, owner: Some(owner), spec: Some(spec) }.compile(&body);
            let mut gs = Vec::new();
            globals_in(&c, &mut gs);
            todo.extend(gs.iter().map(|x| x.0));
            self.p.code.insert(d, c);
        }
        // Builtins (and anything else without a body).
        for d in referenced {
            if self.p.defs.contains_key(&d) {
                continue;
            }
            let info = &g.defs[d as usize];
            let full = format!("{}.{}", info.module, info.name);
            let shape = match checkers_rt::builtins::symbol(&full) {
                Some(sym) => {
                    // Kept: what isn't erased, and for `std.array`'s builtins,
                    // the type parameters, as layouts (D133).
                    let types = checkers_rt::builtins::keeps_types(&full);
                    let mut keep = Vec::new();
                    let mut v = crate::core::eval(g, &std::rc::Rc::new(Vec::new()), &info.ty);
                    let mut k = 0;
                    while let crate::core::Val::Pi(_, m, _, dom, c) = crate::core::force(g, v.clone()) {
                        let is_type = matches!(crate::core::force(g, (*dom).clone()), crate::core::Val::Univ(_));
                        keep.push(m != Mult::Zero || types && is_type);
                        v = crate::core::apply_closure(g, &c, crate::core::Val::var(k));
                        k += 1;
                    }
                    let wrap = self.wrapper(&full, d, FnKind::BuiltinWrap { sym, keep: keep.clone() }, keep.len());
                    DefShape::Builtin { sym, keep, wrap }
                }
                None => DefShape::Missing(full),
            };
            self.p.defs.insert(d, shape);
        }
        // A function is made for each root, and for each definition the
        // code made so far refers to once small functions are inlined:
        // one inlined at every call needs none of its own.
        for d in roots {
            self.shape(*d);
        }
        self.lower_wanted();
    }

    /// The shape of definition `d`. One with code gets its function here,
    /// the first time something refers to it, and is lowered by
    /// `lower_wanted`.
    fn shape(&mut self, d: u32) -> Option<DefShape> {
        if let Some(s) = self.p.defs.get(&d) {
            return Some(s.clone());
        }
        let (n, _) = lams(self.p.code.get(&d)?);
        let func = self.p.funcs.len() as u32;
        let owner = self.p.specs.borrow().origin(d);
        self.p.funcs.push(Func {
            name: self.p.names[owner as usize].clone(),
            owner,
            kind: if n > 0 { FnKind::Global } else { FnKind::Caf },
            params: Vec::new(),
            body: E::Erased,
            nvars: 0,
            rets: 1,
            bounds: HashMap::new(),
        });
        let shape = if n > 0 { DefShape::Fn { func, arity: n } } else { DefShape::Caf { func } };
        self.p.defs.insert(d, shape.clone());
        self.p.wanted.push(d);
        Some(shape)
    }

    /// Lower each definition given a function by `shape` and not lowered
    /// yet, and those they refer to.
    fn lower_wanted(&mut self) {
        while let Some(d) = self.p.wanted.pop() {
            let ir = self.inline_def(d);
            let (DefShape::Fn { func, .. } | DefShape::Caf { func }) = self.p.defs[&d].clone() else { continue };
            self.owner = self.p.specs.borrow().origin(d);
            self.next = 0;
            let (n, body) = lams(&ir);
            let params: Vec<V> = (0..n).map(|_| self.fresh()).collect();
            let bounds = self.param_bounds(d, &params);
            let mut ctx: Vec<V> = params.clone();
            let body = self.expr(body, &mut ctx, true);
            let f = &mut self.p.funcs[func as usize];
            f.params = params;
            f.body = body;
            f.nvars = self.next;
            f.bounds = bounds;
        }
    }

    /// The bounds of the parameters of definition `d`'s code (or of the
    /// function a copy copies, at the parameters the copy takes) that its
    /// signature gives.
    fn param_bounds(&self, d: u32, params: &[V]) -> HashMap<V, Range> {
        let specs = self.p.specs.borrow();
        let (of, binders): (u32, Vec<Option<usize>>) = match specs.copy(d) {
            Some(c) => (c.of.0, c.binders.clone()),
            None => (d, (0..params.len()).map(Some).collect()),
        };
        let Some(b) = self.g.bounds.get(&DefId(of)) else { return HashMap::new() };
        // The last of `b` is the result's.
        let b = &b[..b.len() - 1];
        params.iter().zip(binders).filter_map(|(v, j)| Some((*v, (*b.get(j?)?)?))).collect()
    }

    /// A closed term as a function of no arguments (a `Caf` computed
    /// afresh each time it runs): its index.
    pub fn add_closed(&mut self, t: &Tm) -> u32 {
        let spec = crate::native::spec::SpecCx { table: &self.p.specs, staged: self.staged, depth: 0 };
        let ir = Compiler { g: self.g, owner: None, spec: Some(spec) }.compile(t);
        self.add_closed_ir(&ir)
    }

    /// Closed code as a function of no arguments (see `add_closed`).
    pub fn add_closed_ir(&mut self, ir: &Ir) -> u32 {
        let mut gs = Vec::new();
        globals_in(ir, &mut gs);
        let roots: Vec<u32> = gs.iter().map(|x| x.0).collect();
        self.add_defs(&roots);
        let func = self.p.funcs.len() as u32;
        self.p.funcs.push(Func { name: "check".into(), owner: NO_OWNER, kind: FnKind::Caf, params: Vec::new(), body: E::Erased, nvars: 0, rets: 1, bounds: HashMap::new() });
        self.owner = NO_OWNER;
        self.next = 0;
        let mut ctx = Vec::new();
        let ir = self.inline(ir, None);
        let body = self.expr(&ir, &mut ctx, true);
        let f = &mut self.p.funcs[func as usize];
        f.body = body;
        f.nvars = self.next;
        self.lower_wanted();
        func
    }
}

/// What the runtime's printer calls (#126, #170), as closed code: a pair of
/// the hand-written `Debug` instances' functions (`debug_table`) and the
/// functions computing fields' types from earlier fields (`field_fns`), each
/// a list. `None` if the program has neither.
pub fn show_table(g: &Globals) -> Option<Ir> {
    let (nil, cons) = (g.well_known.nil?, g.well_known.cons?);
    let fields = crate::native::field_fns(g);
    let debug = debug_table(g);
    if debug.is_none() && fields.is_empty() {
        return None;
    }
    let c = Compiler::new(g, None);
    let debug = match debug {
        Some(t) => c.go_pub(&t),
        None => Ir::Con(nil, Vec::new()),
    };
    let fields = fields.iter().rev().fold(Ir::Con(nil, Vec::new()), |rest, (con, k, t)| Ir::Con(cons, vec![Arc::new(c.field_type_fn(*con, *k, t)), Arc::new(rest)]));
    Some(Ir::Tuple(vec![Arc::new(debug), Arc::new(fields)]))
}

impl Lowerer<'_, '_> {
    /// `ir`, the code of `owner`, with small functions inlined (`inline`).
    fn inline(&mut self, ir: &Ir, owner: Option<DefId>) -> Ir {
        let ir = self.inliner(|i| i.program(ir, owner));
        self.float_in(&ir)
    }

    /// Definition `d`'s code, with small functions inlined (`inline`).
    fn inline_def(&mut self, d: u32) -> Ir {
        let ir = self.inliner(|i| i.definition(d)).expect("a definition with code");
        self.float_in(&ir)
    }

    fn inliner<T>(&mut self, f: impl FnOnce(&mut crate::native::inline::Inliner) -> T) -> T {
        let p = &mut *self.p;
        let specs = p.specs.borrow();
        let origin = |d: u32| specs.origin(d);
        f(&mut crate::native::inline::Inliner { code: &p.code, recursive: &mut p.recursive, done: &mut p.inlined, origin: &origin })
    }

    fn float_in(&self, ir: &Ir) -> Ir {
        let defs = &self.p.defs;
        let pure_call = |d: DefId, n: usize| {
            matches!(defs.get(&d.0), Some(DefShape::Builtin { sym, keep, .. }) if keep.len() == n && checkers_rt::builtins::PURE.contains(sym))
        };
        crate::native::inline::float_in(ir, &pure_call)
    }

    fn fresh(&mut self) -> V {
        self.next += 1;
        self.next - 1
    }

    /// A wrapper function (builtin or constructor) of `arity` parameters.
    fn wrapper(&mut self, name: &str, owner: u32, kind: FnKind, arity: usize) -> u32 {
        let params: Vec<V> = (0..arity as u32).collect();
        self.p.funcs.push(Func { name: name.to_string(), owner, kind, params, body: E::Erased, nvars: arity as u32, rets: 1, bounds: HashMap::new() });
        (self.p.funcs.len() - 1) as u32
    }

    fn con_wrap(&mut self, c: u32) -> u32 {
        if let Some(f) = self.p.con_wraps.get(&c) {
            return *f;
        }
        let ci = &self.g.cons[c as usize];
        let np = self.g.arity_ty(ci.ty);
        let erased = ci.fields.iter().map(|f| f.1 == Mult::Zero).collect();
        let name = ci.name.to_string();
        let arity = self.g.arity_con(ConId(c));
        let f = self.wrapper(&name, self.owner, FnKind::ConWrap { con: c, np, erased }, arity);
        self.p.con_wraps.insert(c, f);
        f
    }

    /// A constructor with more than `MAX_ARITY` arguments as a lambda chain,
    /// which `lams` curries.
    fn wide_con_fn(&self, c: ConId) -> Ir {
        let ci = &self.g.cons[c.0 as usize];
        let np = self.g.arity_ty(ci.ty);
        let n = np + ci.fields.len();
        let fields = ci.fields.iter().enumerate().map(|(k, f)| Arc::new(if f.1 == Mult::Zero { Ir::Erased } else { Ir::Var(n - 1 - np - k) })).collect();
        (0..n).fold(Ir::Con(c, fields), |body, _| Ir::Lam(Some(DefId(self.owner)), Arc::new(body)))
    }

    /// An atom for a borrowed position: literals stay; anything else is
    /// bound to a variable first (`binds`, outermost first).
    fn atom(&mut self, e: E, binds: &mut Vec<(V, E)>) -> E {
        match e {
            E::Var(_) | E::Int(_) | E::Str(_) | E::Bytes(_) | E::Static(_) | E::Erased | E::Unit => e,
            other => {
                let v = self.fresh();
                binds.push((v, other));
                E::Var(v)
            }
        }
    }

    fn wrap(binds: Vec<(V, E)>, e: E) -> E {
        binds.into_iter().rev().fold(e, |acc, (v, x)| E::Let(v, Box::new(x), Box::new(acc)))
    }

    fn borrow(&mut self, op: BOp, args: Vec<E>) -> E {
        let mut binds = Vec::new();
        let args = args.into_iter().map(|a| self.atom(a, &mut binds)).collect();
        Self::wrap(binds, E::Borrow { op, args, drops: Vec::new() })
    }

    fn lit(v: &RtLit) -> E {
        match v {
            RtLit::Num(n) if checkers_rt::word::fits(*n) => E::Int(*n as i64),
            RtLit::Num(n) => E::BigLit(n.to_string()),
            RtLit::Big(n) => E::BigLit(n.to_string()),
            RtLit::Str(s) => E::Str(s.clone()),
            RtLit::Bytes(b) => E::Bytes(b.clone()),
        }
    }

    fn expr(&mut self, ir: &Ir, ctx: &mut Vec<V>, tail: bool) -> E {
        match ir {
            Ir::Var(i) => E::Var(ctx[ctx.len() - 1 - i]),
            Ir::Global(d) => {
                self.shape(d.0);
                E::Global(d.0)
            }
            Ir::Erased => E::Erased,
            Ir::Lit(v) => Self::lit(v),
            Ir::Fail(m) => E::Fail(m),
            Ir::At(o, x) => {
                let o = o.map_or(NO_OWNER, |d| d.0);
                if o == self.owner {
                    return self.expr(x, ctx, tail);
                }
                let saved = std::mem::replace(&mut self.owner, o);
                let e = self.expr(x, ctx, tail);
                self.owner = saved;
                E::At(o, Box::new(e))
            }
            Ir::Lam(..) => self.lambda(ir, ctx),
            Ir::ConFn(c) => {
                let arity = self.g.arity_con(*c);
                if arity == 0 {
                    E::Con { con: c.0, fields: Vec::new(), reuse: None }
                } else if arity > MAX_ARITY {
                    self.lambda(&self.wide_con_fn(*c), ctx)
                } else {
                    self.con_wrap(c.0);
                    E::ConFn(c.0)
                }
            }
            Ir::Call(h, args) => self.call(h, args, ctx, tail),
            Ir::Let(v, b) => {
                let ve = self.expr(v, ctx, false);
                let x = self.fresh();
                ctx.push(x);
                let be = self.expr(b, ctx, tail);
                ctx.pop();
                E::Let(x, Box::new(ve), Box::new(be))
            }
            Ir::Tuple(xs) => {
                if xs.is_empty() {
                    return E::Unit;
                }
                Static::fold(E::Tuple(xs.iter().map(|x| self.expr(x, ctx, false)).collect()))
            }
            Ir::Proj(x, i, rest) => {
                let xe = self.expr(x, ctx, false);
                self.borrow(if *rest { BOp::ProjRest(*i) } else { BOp::Proj(*i) }, vec![xe])
            }
            Ir::Field(x, i) => {
                let xe = self.expr(x, ctx, false);
                self.borrow(BOp::Field(*i), vec![xe])
            }
            Ir::Con(c, xs) => Static::fold(E::Con { con: c.0, fields: xs.iter().map(|x| self.expr(x, ctx, false)).collect(), reuse: None }),
            Ir::Prim(op, args, nat) => {
                let es: Vec<E> = args.iter().map(|a| self.expr(a, ctx, false)).collect();
                match op {
                    Op::Par => {
                        // `par t` with a non-literal tuple: the tuple itself.
                        es.into_iter().next().unwrap_or(E::Unit)
                    }
                    _ => self.borrow(BOp::Prim(*op, *nat), es),
                }
            }
            Ir::Par(xs) => {
                let thunks = xs.iter().map(|x| self.thunk(x, ctx)).collect();
                E::Par(thunks)
            }
            Ir::Case(s, c) => {
                let se = self.expr(s, ctx, false);
                let (scrut, binds) = match se {
                    E::Var(v) => (v, Vec::new()),
                    other => {
                        let v = self.fresh();
                        (v, vec![(v, other)])
                    }
                };
                let mut arms = Vec::new();
                for (con, n, body) in &c.branches {
                    let fields: Vec<V> = (0..*n).map(|_| self.fresh()).collect();
                    ctx.extend(fields.iter().copied());
                    let b = self.expr(body, ctx, tail);
                    ctx.truncate(ctx.len() - n);
                    let fv = free_vars(&b);
                    arms.push(Arm { con: con.0, fields: fields.into_iter().map(|f| fv.contains(&f).then_some(f)).collect(), body: b });
                }
                let lits = c.lits.iter().map(|(l, b)| (Self::lit(l), self.expr(b, ctx, tail))).collect();
                let default = c.default.as_ref().map(|d| Box::new(self.expr(d, ctx, tail)));
                Self::wrap(binds, E::Case { scrut, arms, lits, default })
            }
        }
    }

    /// A lambda chain at an expression: a new function, and its closure.
    fn lambda(&mut self, ir: &Ir, ctx: &[V]) -> E {
        let (n, body) = lams(ir);
        // Lower the body in a fresh numbering, mapping the enclosing
        // variables it uses to captured ones.
        let saved_next = self.next;
        let outer: Vec<V> = ctx.to_vec();
        self.next = 0;
        // Placeholders for the outer variables, then the parameters.
        let inner_outer: Vec<V> = (0..outer.len()).map(|_| self.fresh()).collect();
        let params: Vec<V> = (0..n).map(|_| self.fresh()).collect();
        let mut inner_ctx: Vec<V> = inner_outer.clone();
        inner_ctx.extend(params.iter().copied());
        let b = self.expr(body, &mut inner_ctx, true);
        let nvars = self.next;
        self.next = saved_next;
        let fv = free_vars(&b);
        // Captured: outer variables the body uses.
        let mut captured_inner = Vec::new();
        let mut captured_outer = Vec::new();
        for (k, iv) in inner_outer.iter().enumerate() {
            if fv.contains(iv) && !captured_inner.contains(iv) {
                captured_inner.push(*iv);
                captured_outer.push(outer[k]);
            }
        }
        // The same outer variable may appear twice in the context (never in
        // practice): keep the first.
        let f = self.p.funcs.len() as u32;
        let owner = self.owner;
        let name = format!("lambda{f}");
        self.p.funcs.push(Func {
            name,
            owner,
            kind: FnKind::Lambda { captured: captured_inner },
            params,
            body: b,
            nvars,
            rets: 1,
            bounds: HashMap::new(),
        });
        E::MkClo { f, captured: captured_outer }
    }

    /// A `par` component: a closure taking `()`.
    fn thunk(&mut self, x: &Ir, ctx: &[V]) -> E {
        let lam = Ir::Lam(Some(DefId(self.owner)), Arc::new(shift(x, 1)));
        self.lambda(&lam, ctx)
    }

    fn call(&mut self, h: &Ir, args: &[Arc<Ir>], ctx: &mut Vec<V>, tail: bool) -> E {
        if let Ir::Global(d) = h {
            match self.shape(d.0) {
                Some(DefShape::Fn { func, arity }) if args.len() >= arity => {
                    let es: Vec<E> = args[..arity].iter().map(|a| self.expr(a, ctx, false)).collect();
                    let rest: Vec<E> = args[arity..].iter().map(|a| self.expr(a, ctx, false)).collect();
                    if rest.is_empty() {
                        return E::Call { f: func, args: es, tail };
                    }
                    let inner = E::Call { f: func, args: es, tail: false };
                    return E::Apply { f: Box::new(inner), args: rest, tail };
                }
                // A builtin that may update an argument in place is called
                // through its wrapper, which owns its arguments (D133).
                Some(DefShape::Builtin { sym, keep, wrap }) if args.len() >= keep.len() && checkers_rt::builtins::OWNING.contains(&sym) => {
                    let es: Vec<E> = args.iter().map(|a| self.expr(a, ctx, false)).collect();
                    let (now, rest) = es.split_at(keep.len());
                    let call = E::Call { f: wrap, args: now.to_vec(), tail: tail && rest.is_empty() };
                    if rest.is_empty() {
                        return call;
                    }
                    return E::Apply { f: Box::new(call), args: rest.to_vec(), tail };
                }
                Some(DefShape::Builtin { sym, keep, .. }) if args.len() >= keep.len() => {
                    let kept: Vec<E> = args[..keep.len()]
                        .iter()
                        .zip(&keep)
                        .filter(|(_, k)| **k)
                        .map(|(a, _)| a.clone())
                        .collect::<Vec<_>>()
                        .iter()
                        .map(|a| self.expr(a, ctx, false))
                        .collect();
                    let rest: Vec<E> = args[keep.len()..].iter().map(|a| self.expr(a, ctx, false)).collect();
                    let call = self.borrow(BOp::Builtin(sym), kept);
                    if rest.is_empty() {
                        return call;
                    }
                    return E::Apply { f: Box::new(call), args: rest, tail };
                }
                _ => {}
            }
        }
        let f = self.expr(h, ctx, false);
        let es = args.iter().map(|a| self.expr(a, ctx, false)).collect();
        E::Apply { f: Box::new(f), args: es, tail }
    }
}

/// Shift free de Bruijn indices of `ir` up by `k` (for wrapping in a lambda).
fn shift(ir: &Ir, k: usize) -> Ir {
    crate::native::ir::shift(ir, k, 0)
}

/// The definitions code refers to.
pub fn globals_in(ir: &Ir, out: &mut Vec<DefId>) {
    crate::native::ir::globals_in(ir, out)
}

/// Free variables of an expression.
pub fn free_vars(e: &E) -> BTreeSet<V> {
    let mut s = BTreeSet::new();
    fv(e, &mut s);
    s
}

fn fv(e: &E, s: &mut BTreeSet<V>) {
    match e {
        E::Var(v) => {
            s.insert(*v);
        }
        E::Let(x, a, b) => {
            fv(a, s);
            let mut inner = BTreeSet::new();
            fv(b, &mut inner);
            inner.remove(x);
            s.extend(inner);
        }
        E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) => args.iter().for_each(|a| fv(a, s)),
        E::LetMulti(xs, a, b) => {
            fv(a, s);
            let mut inner = BTreeSet::new();
            fv(b, &mut inner);
            for x in xs {
                inner.remove(x);
            }
            s.extend(inner);
        }
        E::Con { fields, reuse, .. } => {
            fields.iter().for_each(|a| fv(a, s));
            if let Some(r) = reuse {
                s.insert(*r);
            }
        }
        E::Apply { f, args, .. } => {
            fv(f, s);
            args.iter().for_each(|a| fv(a, s));
        }
        E::MkClo { captured, .. } => s.extend(captured.iter().copied()),
        E::Borrow { args, drops, .. } => {
            args.iter().for_each(|a| fv(a, s));
            s.extend(drops.iter().copied());
        }
        E::Case { scrut, arms, lits, default } => {
            s.insert(*scrut);
            for a in arms {
                let mut inner = BTreeSet::new();
                fv(&a.body, &mut inner);
                for f in a.fields.iter().flatten() {
                    inner.remove(f);
                }
                s.extend(inner);
            }
            for (_, b) in lits {
                fv(b, s);
            }
            if let Some(d) = default {
                fv(d, s);
            }
        }
        E::Dup(x, b) | E::Drop(x, b) => {
            s.insert(*x);
            fv(b, s);
        }
        E::At(_, b) => fv(b, s),
        E::DropReuse(x, t, _, b) => {
            s.insert(*x);
            let mut inner = BTreeSet::new();
            fv(b, &mut inner);
            inner.remove(t);
            s.extend(inner);
        }
        _ => {}
    }
}
