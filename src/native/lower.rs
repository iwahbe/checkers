//! Closure conversion (#569, §14): erased code (`native::ir::Ir`,
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
    Str(Arc<str>),
    Bytes(Arc<[u8]>),
    /// A value made only of literals, constructors and tuples: static data,
    /// laid out when the program is compiled rather than built each time it
    /// runs. A node of the graph.
    Static(Arc<Static>, u32),
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
    /// `reuse`: memory of a value being dropped, to build in place (#567).
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

/// Static data (`E::Static`, `Ir::Static`): values known when the program
/// is compiled, as a graph of the words and objects they are at run time,
/// each node's parts before it and equal nodes one (§8.9, §14). Code
/// generation lays a value out as immortal objects; every walk over one is
/// a loop over the table or an explicit stack, never recursion, so a value
/// of any depth takes the same stack.
#[derive(Clone, Default)]
pub struct Static {
    nodes: Vec<SNode>,
    /// Each node's hash, of its value: equal values in different graphs
    /// hash alike (code generation lays out each value once).
    hashes: Vec<u128>,
    ids: crate::known::FxMap<SNode, u32>,
}

/// A node of static data.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SNode {
    /// An immediate: a small integer, a constructor without fields, `()`
    /// or an erased value.
    Word(u64),
    /// An integer past a word's 63 bits (a `K_BIG` object).
    Big(num_bigint::BigInt),
    /// Bytes, or a string's bytes (a `K_BYTES` object).
    Bytes(Arc<[u8]>),
    /// A constructor (`K_CON`, its tag) or a tuple (`K_TUPLE`): its fields.
    Obj { kind: u64, tag: u64, fields: Box<[u32]> },
    /// An array (`K_ARRAY`) laid out by `layout`, a word per element or
    /// packed (each element then a number or `Bool`'s word).
    Array { layout: u8, elems: Box<[u32]> },
    /// A definition's function as a value: its global closure.
    Global(u32),
    /// A constructor's function as a value: its wrapper's global closure.
    ConFn(u32),
    /// A function of the program without free variables (a closed
    /// lambda), as a value: its global closure.
    Code(u32),
}

impl SNode {
    /// The nodes it points to (or packs).
    pub fn parts(&self) -> &[u32] {
        match self {
            SNode::Obj { fields, .. } => fields,
            SNode::Array { elems, .. } => elems,
            _ => &[],
        }
    }
}

impl Static {
    pub fn node(&self, id: u32) -> &SNode {
        &self.nodes[id as usize]
    }

    /// The definitions whose functions the value at `id` holds, or `None`
    /// if it holds a function of the program's first-order code.
    pub fn globals(&self, id: u32) -> Option<Vec<u32>> {
        let mut out = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut todo = vec![id];
        while let Some(n) = todo.pop() {
            if !seen.insert(n) {
                continue;
            }
            match self.node(n) {
                SNode::Global(d) => out.push(*d),
                SNode::Code(_) => return None,
                node => todo.extend_from_slice(node.parts()),
            }
        }
        Some(out)
    }

    pub fn hash_of(&self, id: u32) -> u128 {
        self.hashes[id as usize]
    }

    /// Add a node whose fields are nodes already here; an equal node
    /// already here is that one.
    pub fn add(&mut self, n: SNode) -> u32 {
        if let Some(&id) = self.ids.get(&n) {
            return id;
        }
        let hash = crate::known::hash128(|s: &mut dyn std::hash::Hasher| match &n {
            SNode::Obj { kind, tag, fields } => {
                s.write_u8(0);
                s.write_u64(*kind);
                s.write_u64(*tag);
                for f in fields.iter() {
                    s.write(&self.hashes[*f as usize].to_le_bytes());
                }
            }
            SNode::Word(x) => {
                s.write_u8(1);
                s.write_u64(*x);
            }
            SNode::Global(d) => {
                s.write_u8(5);
                s.write_u32(*d);
            }
            SNode::ConFn(c) => {
                s.write_u8(6);
                s.write_u32(*c);
            }
            SNode::Code(f) => {
                s.write_u8(7);
                s.write_u32(*f);
            }
            SNode::Array { layout, elems } => {
                s.write_u8(4);
                s.write_u8(*layout);
                s.write_usize(elems.len());
                for f in elems.iter() {
                    s.write(&self.hashes[*f as usize].to_le_bytes());
                }
            }
            SNode::Big(b) => {
                s.write_u8(2);
                s.write(&b.to_signed_bytes_le());
            }
            SNode::Bytes(b) => {
                s.write_u8(3);
                s.write_usize(b.len());
                s.write(b);
            }
        });
        let id = self.nodes.len() as u32;
        self.nodes.push(n.clone());
        self.hashes.push(hash);
        self.ids.insert(n, id);
        id
    }

    /// The node of a word or a literal `e`, if it is one; or of a function
    /// value whose closure is static (`functions`: whether a definition's
    /// value is its function).
    fn leaf(&mut self, e: &E, functions: &dyn Fn(u32) -> bool) -> Option<u32> {
        use checkers_rt::word as w;
        Some(match e {
            E::Global(d) if functions(*d) => self.add(SNode::Global(*d)),
            E::ConFn(c) => self.add(SNode::ConFn(*c)),
            E::MkClo { f, captured } if captured.is_empty() => self.add(SNode::Code(*f)),
            E::Int(n) => self.add(SNode::Word(w::mk_int(*n))),
            E::Str(s) => self.add(SNode::Bytes(Arc::from(s.as_bytes()))),
            E::Bytes(b) => self.add(SNode::Bytes(b.clone())),
            E::Erased => self.add(SNode::Word(w::ERASED)),
            E::Unit => self.add(SNode::Word(w::UNIT)),
            E::Con { con, fields, reuse: None } if fields.is_empty() => self.add(SNode::Word(w::nullary(*con))),
            _ => return None,
        })
    }

    /// Copy node `id` of `from`, and the nodes it reaches, here: its id here.
    pub fn import(&mut self, from: &Static, id: u32) -> u32 {
        let mut map: crate::known::FxMap<u32, u32> = Default::default();
        for x in from.reachable(id) {
            let n = match from.node(x) {
                SNode::Obj { kind, tag, fields } => SNode::Obj { kind: *kind, tag: *tag, fields: fields.iter().map(|f| map[f]).collect() },
                SNode::Array { layout, elems } => SNode::Array { layout: *layout, elems: elems.iter().map(|f| map[f]).collect() },
                n => n.clone(),
            };
            map.insert(x, self.add(n));
        }
        map[&id]
    }

    /// The nodes `id` reaches, itself included, parts first (in the
    /// table's order).
    pub fn reachable(&self, id: u32) -> Vec<u32> {
        let mut seen = vec![false; id as usize + 1];
        let mut todo = vec![id];
        seen[id as usize] = true;
        while let Some(x) = todo.pop() {
            for &f in self.node(x).parts() {
                if !seen[f as usize] {
                    seen[f as usize] = true;
                    todo.push(f);
                }
            }
        }
        (0..=id).filter(|x| seen[*x as usize]).collect()
    }

    /// A constructor or tuple whose fields are all words, literals or
    /// static data, as one value: static data too. The largest field's
    /// graph is grown, so a long list written out is built in linear time.
    pub fn fold(e: E, functions: &dyn Fn(u32) -> bool) -> E {
        let fields = match &e {
            E::Con { fields, reuse: None, .. } | E::Tuple(fields) if !fields.is_empty() => fields,
            _ => return e,
        };
        if !fields.iter().all(|f| matches!(f, E::Static(..)) || Static::default().leaf(f, functions).is_some()) {
            return e;
        }
        let (con, mut fields) = match e {
            E::Con { con, fields, .. } => (Some(con), fields),
            E::Tuple(xs) => (None, xs),
            _ => unreachable!(),
        };
        // The graph to grow: the largest field's.
        let big = fields.iter().enumerate().filter_map(|(k, f)| if let E::Static(g, _) = f { Some((g.nodes.len(), k)) } else { None }).max().map(|(_, k)| k);
        let mut graph = match big {
            Some(k) => match std::mem::replace(&mut fields[k], E::Unit) {
                E::Static(g, id) => {
                    fields[k] = E::Static(Arc::new(Static::default()), id);
                    Arc::try_unwrap(g).unwrap_or_else(|g| (*g).clone())
                }
                _ => unreachable!(),
            },
            None => Static::default(),
        };
        let ids: Vec<u32> = fields
            .iter()
            .enumerate()
            .map(|(k, f)| match f {
                E::Static(_, id) if Some(k) == big => *id,
                E::Static(g, id) => graph.import(g, *id),
                f => graph.leaf(f, functions).expect("a literal"),
            })
            .collect();
        let id = match con {
            Some(c) => graph.add(SNode::Obj { kind: checkers_rt::word::K_CON, tag: c as u64, fields: ids.into() }),
            None => graph.tuple(ids),
        };
        E::Static(Arc::new(graph), id)
    }

    /// A tuple of nodes: `(a, (b, c))` is `(a, b, c)` (#673).
    pub fn tuple(&mut self, mut ids: Vec<u32>) -> u32 {
        use checkers_rt::word as w;
        if let Some(&last) = ids.last() {
            if let SNode::Obj { kind, fields, .. } = self.node(last) {
                if *kind == w::K_TUPLE && fields.len() >= 2 {
                    let rest = fields.clone();
                    ids.pop();
                    ids.extend(rest.iter().copied());
                }
            }
        }
        self.add(SNode::Obj { kind: w::K_TUPLE, tag: 0, fields: ids.into() })
    }

    /// Node `id` as erased code (`Ir`): its word, or the static data.
    pub fn ir(this: &Arc<Static>, id: u32) -> Ir {
        use checkers_rt::word as w;
        match this.node(id) {
            SNode::Word(x) if *x == w::ERASED => Ir::Erased,
            SNode::Word(x) if *x == w::UNIT => Ir::Tuple(Vec::new()),
            SNode::Word(x) if w::is_int(*x) => Ir::Lit(RtLit::Num(w::int_of(*x) as i128)),
            SNode::Word(x) if *x & 7 == 2 => Ir::Con(ConId((*x >> 3) as u32), Vec::new()),
            _ => Ir::Static(this.clone(), id),
        }
    }

    /// A static constructor taken apart one level: its constructor and its
    /// fields as code.
    pub fn open_con(this: &Arc<Static>, id: u32) -> Option<(ConId, Vec<Arc<Ir>>)> {
        match this.node(id) {
            SNode::Obj { kind, tag, fields } if *kind == checkers_rt::word::K_CON => {
                Some((ConId(*tag as u32), fields.iter().map(|f| Arc::new(Static::ir(this, *f))).collect()))
            }
            _ => None,
        }
    }

    /// Node `id` as code: its word, or the static data.
    pub fn expr(this: &Arc<Static>, id: u32) -> E {
        use checkers_rt::word as w;
        match this.node(id) {
            SNode::Word(x) if *x == w::ERASED => E::Erased,
            SNode::Word(x) if *x == w::UNIT => E::Unit,
            SNode::Word(x) if w::is_int(*x) => E::Int(w::int_of(*x)),
            SNode::Word(x) if *x & 7 == 2 => E::Con { con: (*x >> 3) as u32, fields: Vec::new(), reuse: None },
            _ => E::Static(this.clone(), id),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BOp {
    Prim(Op, bool),
    /// A builtin: its runtime symbol.
    Builtin(&'static str),
    Field(usize),
    Proj(usize),
    /// A tuple's component `i` and the rest after it (#673).
    ProjRest(usize),
    /// `[cell, i, x]`: store `x` (one more reference) in field `i` (an
    /// integer word) of a new constructor cell whose field `i` is empty;
    /// `()`. Only the code `tailrec` writes fills a cell this way.
    SetField,
    /// `[s, acc]`: the accumulator of `f.acc` for `f xs ++ s` (§14) with
    /// the piece `s` in front (`ck_concat_push`): for a list, `s ++ acc`;
    /// for a string, bytes or array, a list of the pieces, `s :: acc`. Only
    /// the code `tailrec` writes accumulates this way.
    ConcatPush,
    /// `[x, acc]`: `x ++` what `ConcatPush` accumulated in `acc`
    /// (`ck_concat_all`), each element copied once.
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
    /// Whether its code is folded (§8.9, `fold`): a program's, not code
    /// compiled to run when compiling.
    pub fold: bool,
    /// Operations on static data alone left to run unkept, which the
    /// check reports as compiler bugs (`CHECKERS_RESIDUAL_CHECK=1`).
    pub residual: Vec<String>,
}

/// Code with no definition (a `check`, a value staging computes).
pub const NO_OWNER: u32 = u32::MAX;

/// Adds to a `Program`.
pub struct Lowerer<'a, 'g: 'a> {
    g: &'g Globals,
    staged: Option<&'a crate::stage::Staged>,
    p: &'a mut Program,
    /// Folds the program's code (`Program::fold`), made when first needed.
    folder: Option<crate::native::fold::Folder<'a>>,
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
pub(crate) fn lams(ir: &Ir) -> (usize, &Ir) {
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
            fold: false,
            residual: Vec::new(),
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
    p.fold = !crate::native::fold::off();
    p.specs.borrow_mut().for_values = true;
    Lowerer::new(g, staged, &mut p).add_defs(&[main.0]);
    p.main = main.0;
    if let Some(ir) = show_table(g) {
        p.debug = Some(Lowerer::new(g, staged, &mut p).add_closed_ir(&ir));
    }
    p
}

impl<'a, 'g> Lowerer<'a, 'g> {
    pub fn new(g: &'g Globals, staged: Option<&'a crate::stage::Staged>, p: &'a mut Program) -> Self {
        Lowerer { g, staged, p, folder: None, next: 0, owner: 0 }
    }

    /// Lower `roots` and every definition they reach that isn't lowered yet.
    pub fn add_defs(&mut self, roots: &[u32]) {
        self.erase(roots);
        // A function is made for each root, and for each definition the
        // code made so far refers to once small functions are inlined:
        // one inlined at every call needs none of its own.
        for d in roots {
            self.shape(*d);
        }
        self.lower_wanted();
    }

    /// Erase `roots` (definitions or copies) and every definition they
    /// reach that isn't erased yet; their functions are made when code
    /// refers to them.
    fn erase(&mut self, roots: &[u32]) {
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
                // One made where a call is folded: erased code already.
                Some((_, crate::native::spec::Body::Folded { code, .. }, _)) => {
                    let mut gs = Vec::new();
                    globals_in(&code, &mut gs);
                    todo.extend(gs.iter().map(|x| x.0));
                    self.p.code.insert(d, code);
                    continue;
                }
                Some((of, crate::native::spec::Body::Term(body), depth)) => (of, Some(body), depth),
                None if (d as usize) < ndefs => (DefId(d), crate::native::ir::body_of(g, staged, DefId(d)), 0),
                None => continue,
            };
            let Some(body) = body else {
                referenced.insert(d);
                continue;
            };
            let spec = crate::native::spec::SpecCx { table: &self.p.specs, staged, depth };
            let c = Compiler::specializing(g, Some(owner), spec).compile(&body);
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
                    // the type parameters, as layouts (#624).
                    let types = checkers_rt::builtins::keeps_types(&full);
                    let mut keep = Vec::new();
                    let mut v = crate::core::eval(g, &crate::core::Env::new(), &info.ty);
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
        let ir = Compiler::specializing(self.g, None, spec).compile(t);
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
        let ir = self.fold(d, ir);
        self.float_in(&ir)
    }

    /// Definition `d`'s code folded (§8.9), if the program's code is; with
    /// `CHECKERS_RESIDUAL_CHECK=1`, each operation on static data alone it
    /// leaves to run and didn't keep reported in `Program::residual`.
    fn fold(&mut self, d: u32, ir: Arc<Ir>) -> Arc<Ir> {
        if !self.p.fold {
            if crate::native::fold::checking() {
                self.check_residual(d, &ir, &[]);
            }
            return ir;
        }
        let (g, staged) = (self.g, self.staged);
        let folder = self.folder.get_or_insert_with(|| crate::native::fold::Folder::new(g, staged));
        // A call passing static data that folding found gets its copy
        // (`spec::specialize_folded`), whose code is added here and folded
        // when it is lowered in turn.
        let (here, depth) = {
            let specs = self.p.specs.borrow();
            (specs.origin(d), specs.copy(d).map_or(0, |c| c.depth))
        };
        let mut made = Vec::new();
        let out = {
            let (code, specs) = (&self.p.code, &self.p.specs);
            let mut copy = |h: u32, args: &[Arc<Ir>]| {
                let r = crate::native::spec::specialize_folded(g, specs, code, here, depth, h, args, &|a| crate::native::fold::is_static(g, a), &crate::native::fold::key);
                made.extend(r.as_ref().map(|(c, _)| c.0));
                r
            };
            folder.fold_def(&ir, specs, &mut copy)
        };
        if !made.is_empty() {
            self.erase(&made);
        }
        let folder = self.folder.as_mut().expect("made above");
        let kept = std::mem::take(&mut folder.kept);
        let name = self.p.names[self.p.specs.borrow().origin(d) as usize].clone();
        if std::env::var_os("CHECKERS_NATIVE_DUMP").is_some() {
            for (node, why) in &kept {
                eprintln!("kept in {name}: {}: {}", crate::native::fold::describe(g, Some(&self.p.specs.borrow()), node), why.why());
            }
        }
        if crate::native::fold::checking() {
            self.check_residual(d, &out, &kept);
        }
        out
    }

    fn check_residual(&mut self, d: u32, ir: &Ir, kept: &[(Arc<Ir>, crate::native::fold::Kept)]) {
        let name = self.p.names[self.p.specs.borrow().origin(d) as usize].clone();
        let mut found = Vec::new();
        crate::native::fold::residuals(self.g, ir, kept, &mut found);
        let what: Vec<String> = found.iter().map(|node| crate::native::fold::describe(self.g, Some(&self.p.specs.borrow()), node)).collect();
        for w in what {
            self.p.residual.push(format!("internal error: `{name}` leaves {w} to run, though every value it needs is known when compiling"));
        }
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

    /// Whether definition `d`'s value is its function, whose closure is
    /// static data (a function or a builtin, not a constant).
    fn is_function(&self, d: u32) -> bool {
        matches!(self.p.defs.get(&d), Some(DefShape::Fn { .. } | DefShape::Builtin { .. }))
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
            E::Var(_) | E::Int(_) | E::Str(_) | E::Bytes(_) | E::Static(..) | E::Erased | E::Unit => e,
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

    fn big(n: num_bigint::BigInt) -> E {
        let mut g = Static::default();
        let id = g.add(SNode::Big(n));
        E::Static(Arc::new(g), id)
    }

    fn lit(v: &RtLit) -> E {
        match v {
            RtLit::Num(n) if checkers_rt::word::fits(*n) => E::Int(*n as i64),
            // Past a word: a static `K_BIG` object (§14).
            RtLit::Num(n) => Self::big(num_bigint::BigInt::from(*n)),
            RtLit::Big(n) => Self::big(n.parse().expect("a number's digits")),
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
            Ir::Static(v, id) => {
                // The functions it holds are compiled.
                for x in v.reachable(*id) {
                    match v.node(x) {
                        SNode::Global(d) => {
                            self.shape(*d);
                        }
                        SNode::ConFn(c) => {
                            self.con_wrap(*c);
                        }
                        _ => {}
                    }
                }
                Static::expr(v, *id)
            }
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
                let e = E::Tuple(xs.iter().map(|x| self.expr(x, ctx, false)).collect());
                Static::fold(e, &|d| self.is_function(d))
            }
            Ir::Proj(x, i, rest) => {
                let xe = self.expr(x, ctx, false);
                self.borrow(if *rest { BOp::ProjRest(*i) } else { BOp::Proj(*i) }, vec![xe])
            }
            Ir::Field(x, i) => {
                let xe = self.expr(x, ctx, false);
                self.borrow(BOp::Field(*i), vec![xe])
            }
            Ir::Con(c, xs) => {
                let e = E::Con { con: c.0, fields: xs.iter().map(|x| self.expr(x, ctx, false)).collect(), reuse: None };
                Static::fold(e, &|d| self.is_function(d))
            }
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
                // through its wrapper, which owns its arguments (#624).
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
