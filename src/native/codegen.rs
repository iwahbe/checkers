//! First-order code → Cranelift (#569, #573, #564).
//!
//! Every function takes its environment (closure) and its arguments as
//! words, in Cranelift's `tail` convention, so calls in tail position are
//! `return_call` (#564). Small integers, `dup`/`drop`, byte indexing and
//! known closure calls are inline; the rest calls the runtime
//! (`checkers_rt`). Global closures, literals and constants' slots are
//! static data.

use super::lower::*;
use super::wide;
use crate::core::Globals;
use crate::core::Prim;
use crate::native::ir::Op;
use crate::range::Range;
use checkers_rt::word as w;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::{I128, I32, I64, I8};
use cranelift_codegen::ir::{
    self, AbiParam, AtomicRmwOp, BlockArg, FuncRef, GlobalValue, InstBuilder, InstructionData, MemFlagsData, Opcode, Signature,
    StackSlotData, StackSlotKind, Value, ValueDef,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use std::collections::{HashMap, HashSet};

/// Runtime functions: name, parameters, whether they return a word.
const RUNTIME: &[(&str, usize, bool)] = &[
    ("ck_alloc", 2, true),
    ("ck_tick", 0, false),
    ("ck_free", 1, false),
    ("ck_add", 2, true),
    ("ck_sub", 2, true),
    ("ck_natsub", 3, true),
    ("ck_mul", 2, true),
    ("ck_div", 3, true),
    ("ck_rem", 3, true),
    ("ck_neg", 1, true),
    ("ck_cmp", 2, true),
    ("ck_eq", 3, true),
    ("ck_ne", 3, true),
    ("ck_concat", 2, true),
    ("ck_concat_own", 2, true),
    ("ck_concat_all", 2, true),
    ("ck_concat_push", 2, true),
    ("ck_len", 1, true),
    ("ck_index", 3, true),
    ("ck_big_lit", 2, true),
    ("ck_fail", 3, true),
    ("ck_error", 3, true),
    ("ck_nomatch", 2, true),
    ("ck_caf", 2, true),
    ("ck_apply", 3, true),
    ("ck_when", 4, true),
    ("ck_par", 2, true),
    ("ck_tuple_flat", 1, true),
    ("ck_tuple_rest", 2, true),
    ("ck_type_apply", 2, true),
];

fn flags() -> MemFlagsData {
    MemFlagsData::trusted()
}

pub struct Gen<'p, M: Module> {
    pub m: M,
    /// The program, which may grow between `define_new`s.
    pub p: Program,
    g: &'p Globals,
    /// Functions of `p` declared and defined so far.
    defined: usize,
    invoke_defined: bool,
    funcs: Vec<FuncId>,
    rt: HashMap<&'static str, FuncId>,
    /// Global closure of a function (definitions, wrappers).
    closures: HashMap<u32, DataId>,
    /// Constants' slots, by definition.
    slots: HashMap<u32, DataId>,
    /// String and bytes literals, by kind and content.
    lits: HashMap<(u64, Vec<u8>), DataId>,
    /// Static data objects laid out so far, for naming the next.
    statics: usize,
    /// Where each value laid out as static data is, by its hash.
    placed: HashMap<u128, Placed>,
    /// Raw bytes (messages, digits).
    raw: HashMap<Vec<u8>, DataId>,
    pub invoke: FuncId,
    /// The functions for numbers within 128 bits (`Wide`) declared so far,
    /// and those of them defined.
    wides: HashMap<Wide, FuncId>,
    wides_defined: HashSet<Wide>,
    true_w: i64,
    false_w: i64,
    max_arity: usize,
    /// With `Some`: each function's name and machine code as text, as it
    /// is defined, with every runtime error's owner written as 0 (for tests
    /// comparing the code of two functions, which name different owners).
    pub disasm: Option<Vec<(String, String)>>,
    /// Compile-time code (§14): each function reads the stack
    /// `checkers_rt::overflow::PROBE` bytes below its frame on entry, so
    /// running out of stack happens in compiled code, where evaluation can
    /// stop safely, and not inside a runtime call.
    pub probe: bool,
}

/// Where a node of static data is.
#[derive(Clone, Copy)]
pub enum Placed {
    Word(u64),
    /// An object, at an offset in a data object.
    Data(DataId, u32),
}

struct St {
    /// Each variable's value. Lowered code defines every variable once, before
    /// its uses and at a point that dominates them (the one loop, a call to
    /// itself in tail position, passes its values as the body's block
    /// parameters), so no Cranelift `Variable`s are needed; the SSA builder
    /// keeps a map per variable as long as the block count, quadratic in
    /// generated code (#67).
    vars: Vec<Option<Value>>,
    /// Values that are never pointers (a comparison's `Bool`): dropping or
    /// duplicating one does nothing, so no code is emitted for it.
    imm: HashSet<Value>,
    /// Values known to be small integers where code is being emitted: an
    /// arithmetic operation's operands on its fast path, a `%`'s result,
    /// `x` in the arm where `x == 3` holds. (Constants are seen in the
    /// code itself, `small`.) Facts that hold only in some blocks are
    /// added before emitting those blocks and removed after.
    ints: HashSet<Value>,
    /// A comparison's `Bool` word: the condition it was made from, so a
    /// `match` on it branches on the comparison itself.
    conds: HashMap<Value, Cond>,
    /// Constant bounds of integers, true wherever the value is: a
    /// parameter's from its type (`Func::bounds`), an operation's from its
    /// operands'. One within the small integers is one.
    bounds: HashMap<Value, Range>,
    owner: u32,
    frefs: HashMap<FuncId, FuncRef>,
    gvs: HashMap<DataId, GlobalValue>,
    /// The function being defined and the block its body starts at: a
    /// call to itself in tail position jumps there, a loop rather than a
    /// call (no frame torn down and set up again).
    this: Option<(u32, ir::Block)>,
    /// The operands of the function's `/`s that a `%` has too: the first
    /// of the two emitted gives the other's result (`Quot`).
    pairs: HashSet<Pair>,
    /// The other result of a `/` or `%` emitted where code is being
    /// emitted now, by its operands. A `match`'s arms each start from what
    /// was known before it.
    quots: HashMap<Pair, Quot>,
    /// What the headers of a loop's arrays say (`loop_arrays`), read once
    /// before it, by the loop's value of each.
    arrays: HashMap<Value, ArrayFacts>,
}

/// An array's header (or any value's, when it isn't one), read once.
#[derive(Clone, Copy)]
struct ArrayFacts {
    /// Its length's word, if it is bytes or an array; else 0, which is no
    /// integer's word.
    len: Value,
    /// Where its elements are, if it is bytes or an array of words (with
    /// `WORDS_BIT` set, which no address has); else 0.
    data: Value,
}

/// Marks an array of words' elements in `ArrayFacts::data`: user space's
/// addresses are below 2^63 (at most 57 bits, on the machines code is
/// generated for).
const WORDS_BIT: i64 = i64::MIN;

impl St {
    fn new(vars: Vec<Option<Value>>, owner: u32, pairs: HashSet<Pair>) -> St {
        St {
            vars,
            imm: HashSet::new(),
            ints: HashSet::new(),
            conds: HashMap::new(),
            bounds: HashMap::new(),
            owner,
            frefs: HashMap::new(),
            gvs: HashMap::new(),
            this: None,
            pairs,
            quots: HashMap::new(),
            arrays: HashMap::new(),
        }
    }
}

/// A division's operands: variables or integer constants.
type Pair = (Atom, Atom);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Atom {
    Var(V),
    Int(i64),
}

impl Atom {
    fn of(e: &E) -> Option<Atom> {
        match e {
            E::Var(v) => Some(Atom::Var(*v)),
            E::Int(n) => Some(Atom::Int(*n)),
            _ => None,
        }
    }
}

/// What a `/` or `%` gives the other of its pair: the remainder (`rem`)
/// or the quotient as a small integer's word, or 0 where it isn't one or
/// the runtime divided. One word, so that keeping it costs little: a
/// remainder by a small integer is always one.
#[derive(Clone, Copy)]
struct Quot {
    rem: bool,
    word: Value,
}

/// An operation on numbers within 128 bits, for which each program has a
/// function of its own (`Gen::define_wide`), called where the operation's
/// operands aren't small integers or its result isn't one; past 128 bits
/// it goes on to the runtime. Called, not inline: the code of small
/// integers' operations, which is most code, keeps the registers it would
/// have without it (measured: inline, the 128-bit paths cost loops on small
/// integers up to 2% more instructions in spills).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Wide {
    Add,
    Sub,
    Mul,
    Neg,
    NatSub,
    Cmp,
    Eq,
    Div,
    Rem,
}

impl Wide {
    fn name(self) -> &'static str {
        match self {
            Wide::Add => "ckw_add",
            Wide::Sub => "ckw_sub",
            Wide::Mul => "ckw_mul",
            Wide::Neg => "ckw_neg",
            Wide::NatSub => "ckw_natsub",
            Wide::Cmp => "ckw_cmp",
            Wide::Eq => "ckw_eq",
            Wide::Div => "ckw_div",
            Wide::Rem => "ckw_rem",
        }
    }

    fn sig(self) -> Signature {
        let mut s = Signature::new(CallConv::Tail);
        let (params, rets) = match self {
            Wide::Neg => (1, 1),
            Wide::Add | Wide::Sub | Wide::Mul | Wide::Cmp => (2, 1),
            Wide::NatSub | Wide::Eq => (3, 1),
            Wide::Div | Wide::Rem => (3, 2),
        };
        s.params.extend((0..params).map(|_| AbiParam::new(I64)));
        s.returns.extend((0..rets).map(|_| AbiParam::new(I64)));
        s
    }
}

/// Each expression in `e`, `e` first: what code is emitted for (not a
/// literal pattern's own expression).
fn each_e(e: &E, f: &mut dyn FnMut(&E)) {
    f(e);
    match e {
        E::Borrow { args, .. } | E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) => args.iter().for_each(|a| each_e(a, f)),
        E::Apply { f: g, args, .. } => {
            each_e(g, f);
            args.iter().for_each(|a| each_e(a, f))
        }
        E::Con { fields, .. } => fields.iter().for_each(|a| each_e(a, f)),
        E::Let(_, a, b) | E::LetMulti(_, a, b) => {
            each_e(a, f);
            each_e(b, f)
        }
        E::Dup(_, b) | E::Drop(_, b) | E::DropReuse(_, _, _, b) | E::At(_, b) => each_e(b, f),
        E::Case { arms, lits, default, .. } => {
            arms.iter().for_each(|a| each_e(&a.body, f));
            lits.iter().for_each(|(_, b)| each_e(b, f));
            if let Some(d) = default {
                each_e(d, f)
            }
        }
        _ => {}
    }
}

/// The operands of each `/` that a `%` has too, in `e`.
fn div_pairs(e: &E) -> HashSet<Pair> {
    let (mut divs, mut rems) = (HashSet::new(), HashSet::new());
    each_e(e, &mut |e| {
        if let E::Borrow { op: BOp::Prim(p @ (Op::Div | Op::Rem), _), args, .. } = e {
            if let [Some(x), Some(y)] = [Atom::of(&args[0]), Atom::of(&args[1])] {
                if *p == Op::Div { &mut divs } else { &mut rems }.insert((x, y));
            }
        }
    });
    divs.retain(|p| rems.contains(p));
    divs
}

/// The parameters of function `me` (`params`) that a loop over its body
/// reads the length or elements of (`len xs`, `xs[i]`) and that every
/// call of itself passes on unchanged: what their headers say is the same
/// at each turn of the loop.
fn loop_arrays(me: u32, params: &[V], body: &E) -> Vec<V> {
    let mut kept = vec![true; params.len()];
    let mut read = HashSet::new();
    let mut looped = false;
    each_e(body, &mut |e| match e {
        // Every call of itself, in tail position or not: emitted in tail
        // position, it jumps back to the loop's start.
        E::Call { f, args, .. } if *f == me => {
            looped = true;
            for (k, a) in args.iter().enumerate() {
                if !matches!(a, E::Var(v) if Some(v) == params.get(k)) {
                    kept[k] = false;
                }
            }
        }
        E::Borrow { op: BOp::Prim(Op::Len | Op::Index, _), args, .. } => {
            if let Some(E::Var(v)) = args.first() {
                read.insert(*v);
            }
        }
        _ => {}
    });
    if !looped {
        return Vec::new();
    }
    params.iter().zip(kept).filter(|(v, k)| *k && read.contains(*v)).map(|(v, _)| *v).collect()
}

/// The machine code `ctx` holds as text, each function it calls named
/// by its symbol (`ck_len`) rather than its number in the function.
fn named_code(m: &impl Module, ctx: &cranelift_codegen::Context) -> String {
    let mut code = ctx.compiled_code().and_then(|c| c.vcode.clone()).unwrap_or_default();
    // Longest numbers first, so `userextname1` doesn't rename the start
    // of `userextname12`.
    let mut names: Vec<(String, String)> = ctx
        .func
        .params
        .user_named_funcs()
        .iter()
        .map(|(r, n)| {
            let decls = m.declarations();
            // `cranelift_module` names functions in namespace 0, data in 1.
            let name = if n.namespace == 1 {
                let id = DataId::from_u32(n.index);
                decls.get_data_decl(id).linkage_name(id).to_string()
            } else {
                let id = FuncId::from_u32(n.index);
                decls.get_function_decl(id).linkage_name(id).to_string()
            };
            (format!("userextname{}", r.as_u32()), name)
        })
        .collect();
    names.sort_by_key(|(k, _)| std::cmp::Reverse(k.len()));
    for (k, v) in names {
        code = code.replace(&k, &v);
    }
    code
}

/// A comparison's condition (`I8`), and what holds when it is true or false.
#[derive(Clone)]
struct Cond {
    c: Value,
    /// Small integers when it is true (`x == 3`: `x`), and when false (`x != 3`).
    small_if: [Vec<Value>; 2],
    /// The comparison `x op y` it is, for the bounds each side gives its
    /// operands (`i < len xs`: `i` is below the largest length).
    rel: Option<(Op, Value, Value)>,
}

#[derive(Clone, Copy)]
enum Mode<'a> {
    /// Return the value: one word, or this many (`unbox`).
    Tail(usize),
    /// Jump to this block with the value.
    Val(ir::Block),
    /// The value is matched at once on constructors without fields: a
    /// constructor or a comparison goes straight to its arm (`Join`).
    Join(&'a Join<'a>),
}

/// `let x = a` followed by a `match` on `x` whose arms are constructors
/// without fields (`Bool`s): `a`'s branches that end in a constructor or a
/// comparison go to the arm it selects, rather than making the word and
/// testing it again (an `and` of comparisons is a branch on each). An arm
/// reached from one place in `a` is emitted there, where what led to it
/// (`i < len xs`) is known; one reached from several, once in a block of
/// its own.
struct Join<'a> {
    x: V,
    /// `x` is dropped before the `match`.
    drop_x: bool,
    arms: &'a [Arm],
    default: Option<&'a E>,
    /// Where the arms' values go.
    outer: Mode<'a>,
    /// How many of `a`'s branches end in each arm's constructor (the last:
    /// the default's).
    reach: Vec<usize>,
    state: std::cell::RefCell<JoinState>,
    /// What was known of quotients before `a`, for the arms' own blocks.
    quots: HashMap<Pair, Quot>,
}

#[derive(Default)]
struct JoinState {
    /// The arms already emitted where they were reached.
    inline: Vec<bool>,
    /// Each arm's own block, taking `x`'s word, once one is needed.
    blocks: Vec<Option<ir::Block>>,
    /// Where any other value of `a` goes, to be matched: a block taking it.
    other: Option<ir::Block>,
}

fn tail_sig(n: usize) -> Signature {
    tail_sig_rets(n, 1)
}

/// A function of `n` arguments (and its environment) returning `rets` words.
fn tail_sig_rets(n: usize, rets: usize) -> Signature {
    let mut s = Signature::new(CallConv::Tail);
    for _ in 0..=n {
        s.params.push(AbiParam::new(I64));
    }
    for _ in 0..rets {
        s.returns.push(AbiParam::new(I64));
    }
    s
}

/// The most words a function of the `tail` calling convention returns in
/// registers on `isa`, up to `unbox::MAX_PARTS`: past them Cranelift would
/// need a return area (8 on x86-64; 6 on ARM64, whose `tail` convention
/// keeps `x0` and `x1` for itself).
pub fn return_words(isa: &dyn cranelift_codegen::isa::TargetIsa) -> usize {
    (1..=super::unbox::MAX_PARTS).rev().find(|n| returns_in_registers(isa, *n)).unwrap_or(1)
}

/// Whether a function returning `n` words compiles on `isa`.
fn returns_in_registers(isa: &dyn cranelift_codegen::isa::TargetIsa, n: usize) -> bool {
    let mut func = ir::Function::with_name_signature(ir::UserFuncName::default(), tail_sig_rets(0, n));
    let mut fctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut func, &mut fctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let zero = b.ins().iconst(I64, 0);
        b.ins().return_(&vec![zero; n]);
        b.seal_all_blocks();
        b.finalize(isa.frontend_config());
    }
    let mut ctx = cranelift_codegen::Context::for_function(func);
    ctx.compile(isa, &mut Default::default()).is_ok()
}

fn arity_of(f: &Func) -> usize {
    match &f.kind {
        FnKind::Caf => 0,
        _ => f.params.len(),
    }
}

impl<'p, M: Module> Gen<'p, M> {
    pub fn new(m: M, p: Program, g: &'p Globals) -> Self {
        Self::with_invoke(m, p, g, Linkage::Export)
    }

    /// JIT modules share the host's dispatcher; object files define their own.
    pub fn importing_invoke(m: M, p: Program, g: &'p Globals) -> Self {
        Self::with_invoke(m, p, g, Linkage::Import)
    }

    fn with_invoke(mut m: M, p: Program, g: &'p Globals, linkage: Linkage) -> Self {
        let call_conv = m.isa().default_call_conv();
        let mut rt = HashMap::new();
        for (name, n, ret) in RUNTIME {
            let mut s = Signature::new(call_conv);
            for _ in 0..*n {
                s.params.push(AbiParam::new(I64));
            }
            if *ret {
                s.returns.push(AbiParam::new(I64));
            }
            rt.insert(*name, m.declare_function(name, Linkage::Import, &s).expect("declare a runtime function"));
        }
        for (_, sym, _) in checkers_rt::builtins::all() {
            if !rt.contains_key(sym) {
                let mut s = Signature::new(call_conv);
                s.params.push(AbiParam::new(I64));
                s.params.push(AbiParam::new(I64));
                s.returns.push(AbiParam::new(I64));
                rt.insert(*sym, m.declare_function(sym, Linkage::Import, &s).expect("declare a builtin"));
            }
        }
        let funcs = Vec::new();
        let max_arity = MAX_ARITY;
        let mut is = Signature::new(call_conv);
        for _ in 0..4 {
            is.params.push(AbiParam::new(I64));
        }
        is.returns.push(AbiParam::new(I64));
        let invoke = m.declare_function("ck_invoke", linkage, &is).expect("declare invoke");
        let wk = &g.well_known;
        let nul = |c: Option<crate::core::ConId>| c.map_or(0, |c| w::nullary(c.0) as i64);
        Gen {
            m,
            p,
            g,
            defined: 0,
            invoke_defined: linkage == Linkage::Import,
            funcs,
            rt,
            closures: HashMap::new(),
            slots: HashMap::new(),
            lits: HashMap::new(),
            statics: 0,
            placed: HashMap::new(),
            raw: HashMap::new(),
            invoke,
            wides: HashMap::new(),
            wides_defined: HashSet::new(),
            true_w: nul(wk.true_con),
            false_w: nul(wk.false_con),
            max_arity,
            disasm: None,
            probe: false,
        }
    }

    // ── static data ─────────────────────────────────────────────────────────

    /// The global closure of function `f` (no free variables).
    fn closure(&mut self, f: u32) -> DataId {
        // A function with borrowed parameters is entered through code
        // taking them owned, as a closure's arguments are.
        let f = self.p.entries.get(&f).copied().unwrap_or(f);
        assert!(!self.p.borrowed.contains_key(&f), "a closure of `{}`, which borrows parameters", self.p.funcs[f as usize].name);
        if let Some(d) = self.closures.get(&f) {
            return *d;
        }
        let id = self.m.declare_data(&format!("ckc_{f}"), Linkage::Local, true, false).expect("declare a closure");
        let mut dd = DataDescription::new();
        let arity = arity_of(&self.p.funcs[f as usize]) as u64;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&w::STATIC_RC.to_le_bytes());
        bytes.extend_from_slice(&w::info(w::K_CLO, 0, arity).to_le_bytes());
        bytes.extend_from_slice(&0u64.to_le_bytes());
        dd.define(bytes.into_boxed_slice());
        dd.set_align(8);
        let fref = self.m.declare_func_in_data(self.funcs[f as usize], &mut dd);
        dd.write_function_addr(16, fref);
        self.m.define_data(id, &dd).expect("define a closure");
        self.closures.insert(f, id);
        id
    }

    fn slot(&mut self, d: u32) -> DataId {
        if let Some(x) = self.slots.get(&d) {
            return *x;
        }
        let id = self.m.declare_data(&format!("cks_{d}"), Linkage::Local, true, false).expect("declare a slot");
        let mut dd = DataDescription::new();
        dd.define(w::UNSET.to_le_bytes().to_vec().into_boxed_slice());
        dd.set_align(8);
        self.m.define_data(id, &dd).expect("define a slot");
        self.slots.insert(d, id);
        id
    }

    fn lit(&mut self, kind: u64, b: &[u8]) -> DataId {
        let key = (kind, b.to_vec());
        if let Some(x) = self.lits.get(&key) {
            return *x;
        }
        let id = self.m.declare_data(&format!("ckl_{}", self.lits.len()), Linkage::Local, true, false).expect("declare a literal");
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&w::STATIC_RC.to_le_bytes());
        bytes.extend_from_slice(&w::info(kind, 0, 0).to_le_bytes());
        bytes.extend_from_slice(&(b.len() as u64).to_le_bytes());
        // Not a slice: the bytes follow (#169).
        bytes.extend_from_slice(&0u64.to_le_bytes());
        bytes.extend_from_slice(b);
        while bytes.len() % 8 != 0 {
            bytes.push(0);
        }
        let mut dd = DataDescription::new();
        dd.define(bytes.into_boxed_slice());
        dd.set_align(8);
        self.m.define_data(id, &dd).expect("define a literal");
        self.lits.insert(key, id);
        id
    }

    /// Where node `id` of static data is: its word, or its object (a data
    /// object and the offset in it). The nodes it reaches that no earlier
    /// static data has are laid out in one new data object, parts first,
    /// as immortal objects (§14); the rest, and literals' bytes, are the
    /// objects already laid out, so equal values are one object in the
    /// program. A loop over the nodes: any depth takes the same stack.
    /// The table of hand-written `Debug` instances (`lower::show_table`), as
    /// the static data its code computes: definitions' and closed lambdas'
    /// functions, laid out when the program is compiled (§8.9), so nothing
    /// builds it when the program starts.
    pub fn debug_table(&mut self) -> Option<Placed> {
        let f = self.p.debug?;
        let (v, id) = match &self.p.funcs[f as usize].body {
            E::Static(v, id) => (v.clone(), *id),
            body => panic!("the `Debug` table is static data, not {}", super::dump(body, 0)),
        };
        Some(self.statik(&v, id))
    }

    fn statik(&mut self, v: &Static, id: u32) -> Placed {
        if let SNode::Word(x) = v.node(id) {
            return Placed::Word(*x);
        }
        if let Some(p) = self.placed.get(&v.hash_of(id)) {
            return *p;
        }
        let data = self.m.declare_data(&format!("ckd_{}", self.statics), Linkage::Local, true, false).expect("declare static data");
        self.statics += 1;
        let mut out: Vec<u8> = Vec::new();
        // Each word that points to an object: where, to which.
        let mut relocs: Vec<(usize, DataId, u32)> = Vec::new();
        let mut at: HashMap<u32, Placed> = HashMap::new();
        for x in v.reachable(id) {
            let h = v.hash_of(x);
            let placed = match v.node(x) {
                SNode::Word(w) => Placed::Word(*w),
                _ if self.placed.contains_key(&h) => self.placed[&h],
                SNode::Bytes(bs) if self.lits.contains_key(&(w::K_BYTES, bs.to_vec())) => Placed::Data(self.lits[&(w::K_BYTES, bs.to_vec())], 0),
                SNode::Bytes(bs) => Placed::Data(data, Self::lay_out_bytes(w::K_BYTES, bs, &mut out) as u32),
                SNode::Big(n) => Placed::Data(data, Self::lay_out_big(n, &mut out) as u32),
                SNode::Global(d) => match self.p.defs.get(d).cloned() {
                    Some(DefShape::Fn { func, .. }) => Placed::Data(self.closure(func), 0),
                    Some(DefShape::Builtin { wrap, .. }) => Placed::Data(self.closure(wrap), 0),
                    _ => unreachable!("a known closure of a function"),
                },
                SNode::ConFn(c) => {
                    let f = self.p.con_wraps[c];
                    Placed::Data(self.closure(f), 0)
                }
                SNode::Code(f) => Placed::Data(self.closure(*f), 0),
                SNode::Lam(_) => unreachable!("a lambda's code made a function when lowered"),
                SNode::Obj { kind, tag, fields } => {
                    let off = out.len();
                    out.extend_from_slice(&w::STATIC_RC.to_le_bytes());
                    // A partial application's count is of its arguments, after
                    // its function.
                    let n = if *kind == w::K_PAP { fields.len() - 1 } else { fields.len() };
                    out.extend_from_slice(&w::info(*kind, n as u64, *tag).to_le_bytes());
                    for (k, f) in fields.iter().enumerate() {
                        match at[f] {
                            Placed::Word(word) => out.extend_from_slice(&word.to_le_bytes()),
                            Placed::Data(d, o) => {
                                relocs.push((off + w::HDR + 8 * k, d, o));
                                out.extend_from_slice(&0u64.to_le_bytes());
                            }
                        }
                    }
                    Placed::Data(data, off as u32)
                }
                SNode::Array { layout, elems } => Placed::Data(data, self.lay_out_array(v, *layout, elems, &at, &mut out, &mut relocs) as u32),
            };
            if matches!(placed, Placed::Data(d, _) if d == data) {
                self.placed.insert(h, placed);
            }
            at.insert(x, placed);
        }
        let mut dd = DataDescription::new();
        dd.define(out.into_boxed_slice());
        dd.set_align(8);
        let mut gvs: HashMap<DataId, cranelift_codegen::ir::GlobalValue> = HashMap::new();
        for (slot, d, o) in relocs {
            let gv = *gvs.entry(d).or_insert_with(|| self.m.declare_data_in_data(d, &mut dd));
            dd.write_data_addr(slot as u32, gv, o as i64);
        }
        self.m.define_data(data, &dd).expect("define static data");
        at[&id]
    }

    /// Append a `K_ARRAY` object to `out`: its length, `0` (not a slice),
    /// then its elements, a word each or packed by `layout`. Its offset.
    fn lay_out_array(&self, v: &Static, layout: u8, elems: &[u32], at: &HashMap<u32, Placed>, out: &mut Vec<u8>, relocs: &mut Vec<(usize, DataId, u32)>) -> usize {
        use checkers_rt::array::Layout;
        let l = Layout::of_code(layout as u64);
        let off = out.len();
        out.extend_from_slice(&w::STATIC_RC.to_le_bytes());
        out.extend_from_slice(&w::info(checkers_rt::array::K_ARRAY, 0, layout as u64).to_le_bytes());
        out.extend_from_slice(&(elems.len() as u64).to_le_bytes());
        out.extend_from_slice(&0u64.to_le_bytes());
        for e in elems {
            // A packed element's number (or truth).
            let n = || -> i128 {
                match v.node(*e) {
                    SNode::Word(x) if w::is_int(*x) => w::int_of(*x) as i128,
                    SNode::Word(x) => (*x as i64 == self.true_w) as i128,
                    SNode::Big(b) => i128::try_from(b).expect("a packed element in its layout's range"),
                    _ => unreachable!("a packed element is a number"),
                }
            };
            match l {
                Layout::Words => match at[e] {
                    Placed::Word(word) => out.extend_from_slice(&word.to_le_bytes()),
                    Placed::Data(d, o) => {
                        relocs.push((out.len(), d, o));
                        out.extend_from_slice(&0u64.to_le_bytes());
                    }
                },
                _ => out.extend_from_slice(&n().to_le_bytes()[..l.width()]),
            }
        }
        while !out.len().is_multiple_of(8) {
            out.push(0);
        }
        off
    }

    /// Append a `K_BIG` object for `n` (past a word) to `out`: its offset.
    fn lay_out_big(n: &num_bigint::BigInt, out: &mut Vec<u8>) -> usize {
        let at = out.len();
        out.extend_from_slice(&w::STATIC_RC.to_le_bytes());
        match i128::try_from(n) {
            Ok(s) => {
                out.extend_from_slice(&checkers_rt::obj::INFO_I128.to_le_bytes());
                out.extend_from_slice(&(s as u128 as u64).to_le_bytes());
                out.extend_from_slice(&(((s as u128) >> 64) as u64).to_le_bytes());
            }
            Err(_) => {
                let (sign, mut mag) = n.to_bytes_le();
                while !mag.len().is_multiple_of(8) {
                    mag.push(0);
                }
                let tag = if sign == num_bigint::Sign::Minus { checkers_rt::obj::BIG_LIMBS_NEG } else { checkers_rt::obj::BIG_LIMBS };
                out.extend_from_slice(&w::info(w::K_BIG, (mag.len() / 8) as u64, tag).to_le_bytes());
                out.extend_from_slice(&mag);
            }
        }
        at
    }

    fn lay_out_bytes(kind: u64, b: &[u8], out: &mut Vec<u8>) -> usize {
        let at = out.len();
        out.extend_from_slice(&w::STATIC_RC.to_le_bytes());
        out.extend_from_slice(&w::info(kind, 0, 0).to_le_bytes());
        out.extend_from_slice(&(b.len() as u64).to_le_bytes());
        out.extend_from_slice(&0u64.to_le_bytes());
        out.extend_from_slice(b);
        while !out.len().is_multiple_of(8) {
            out.push(0);
        }
        at
    }

    fn raw(&mut self, b: &[u8]) -> DataId {
        if let Some(x) = self.raw.get(b) {
            return *x;
        }
        let id = self.m.declare_data(&format!("ckr_{}", self.raw.len()), Linkage::Local, false, false).expect("declare bytes");
        let mut dd = DataDescription::new();
        let mut v = b.to_vec();
        v.push(0);
        dd.define(v.into_boxed_slice());
        self.m.define_data(id, &dd).expect("define bytes");
        self.raw.insert(b.to_vec(), id);
        id
    }

    // ── functions ───────────────────────────────────────────────────────────

    /// Declare and define the functions added to the program since the last
    /// call (and, the first time, `ck_invoke`).
    pub fn define_new(&mut self) {
        let mut fctx = FunctionBuilderContext::new();
        let mut ctx = self.m.make_context();
        for i in self.funcs.len()..self.p.funcs.len() {
            let n = arity_of(&self.p.funcs[i]);
            assert!(n <= MAX_ARITY, "`{}` takes {n} arguments: lowering curries past {MAX_ARITY}", self.p.funcs[i].name);
            let sig = tail_sig_rets(n, self.p.funcs[i].rets);
            let id = self.m.declare_function(&format!("ckf_{i}"), Linkage::Local, &sig).expect("declare a function");
            self.funcs.push(id);
        }
        for i in self.defined..self.p.funcs.len() {
            ctx.func.signature = tail_sig_rets(arity_of(&self.p.funcs[i]), self.p.funcs[i].rets);
            ctx.func.name = ir::UserFuncName::user(0, i as u32);
            {
                let mut b = FunctionBuilder::new(&mut ctx.func, &mut fctx);
                self.function(&mut b, i);
                b.seal_all_blocks();
                b.finalize(self.m.isa().frontend_config());
            }
            ctx.set_disasm(self.disasm.is_some());
            if let Err(e) = self.m.define_function(self.funcs[i], &mut ctx) {
                panic!("native code for `{}`: {e:?}", self.p.funcs[i].name);
            }
            if let Some(d) = &mut self.disasm {
                d.push((self.p.funcs[i].name.clone(), named_code(&self.m, &ctx)));
            }
            self.m.clear_context(&mut ctx);
        }
        self.defined = self.p.funcs.len();
        let mut wides: Vec<Wide> = self.wides.keys().filter(|w| !self.wides_defined.contains(w)).copied().collect();
        wides.sort_by_key(|w| *w as u8);
        for w in wides {
            self.define_wide(&mut fctx, &mut ctx, w);
            self.wides_defined.insert(w);
        }
        if !self.invoke_defined {
            self.define_invoke(&mut fctx, &mut ctx);
            self.invoke_defined = true;
        }
    }

    /// The finished function of index `f` (after `define_new`).
    pub fn func_id(&self, f: u32) -> FuncId {
        self.funcs[f as usize]
    }

    fn function(&mut self, b: &mut FunctionBuilder, i: usize) {
        let f = self.p.funcs[i].clone();
        let f = &f;
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        if self.probe {
            // A load that may trap, so it is kept though its value isn't used.
            let sp = b.ins().get_stack_pointer(I64);
            b.ins().load(I64, MemFlagsData::new(), sp, -(checkers_rt::overflow::PROBE as i32));
        }
        let params: Vec<Value> = b.block_params(entry).to_vec();
        let vars = vec![None; f.nvars.max(f.params.len() as u32) as usize];
        let mut st = St::new(vars, f.owner, div_pairs(&f.body));
        let env = params[0];
        match &f.kind {
            FnKind::Global | FnKind::Caf => {
                // The body starts at a block of its own, which a call to
                // itself in tail position jumps back to.
                let top = b.create_block();
                let arrays: Vec<(usize, ArrayFacts)> = loop_arrays(i as u32, &f.params, &f.body)
                    .into_iter()
                    .map(|v| {
                        let k = f.params.iter().position(|p| *p == v).expect("a parameter");
                        (k, self.array_facts(b, params[k + 1]))
                    })
                    .collect();
                let args: Vec<BlockArg> = params.iter().map(|p| BlockArg::Value(*p)).collect();
                let params: Vec<Value> = params.iter().map(|_| b.append_block_param(top, I64)).collect();
                b.ins().jump(top, &args);
                b.switch_to_block(top);
                for (k, facts) in arrays {
                    st.arrays.insert(params[k + 1], facts);
                }
                self.tick(b, &mut st);
                st.this = Some((i as u32, top));
                for (k, v) in f.params.iter().enumerate() {
                    st.vars[*v as usize] = Some(params[k + 1]);
                    if let Some(r) = f.bounds.get(v) {
                        st.bounds.insert(params[k + 1], *r);
                    }
                }
                self.emit(b, &mut st, &f.body, Mode::Tail(f.rets));
            }
            FnKind::Lambda { captured } => {
                self.tick(b, &mut st);
                for (k, v) in f.params.iter().enumerate() {
                    st.vars[*v as usize] = Some(params[k + 1]);
                }
                for (k, v) in captured.iter().enumerate() {
                    let x = b.ins().load(I64, flags(), env, (w::HDR + 8 + 8 * k) as i32);
                    self.dup(b, &mut st, x);
                    st.vars[*v as usize] = Some(x);
                }
                self.drop_v(b, &mut st, env);
                self.emit(b, &mut st, &f.body, Mode::Tail(f.rets));
            }
            FnKind::BuiltinWrap { sym, keep } => {
                let kept: Vec<Value> = keep.iter().enumerate().filter(|(_, k)| **k).map(|(j, _)| params[j + 1]).collect();
                let r = self.call_array(b, &mut st, sym, &kept);
                for p in &params[1..] {
                    self.drop_v(b, &mut st, *p);
                }
                b.ins().return_(&[r]);
            }
            FnKind::ConWrap { con, np, erased } => {
                let mut fields = Vec::new();
                for (k, p) in params[1..].iter().enumerate() {
                    if k < *np || erased.get(k - np).copied().unwrap_or(false) {
                        self.drop_v(b, &mut st, *p);
                        if k >= *np {
                            fields.push(b.ins().iconst(I64, 0));
                        }
                    } else {
                        fields.push(*p);
                    }
                }
                let r = self.build_con(b, &mut st, *con, &fields, None);
                b.ins().return_(&[r]);
            }
        }
    }

    /// What `x`'s header says, if it is bytes or an array (`ArrayFacts`).
    fn array_facts(&mut self, b: &mut FunctionBuilder, x: Value) -> ArrayFacts {
        let obj = b.create_block();
        let arr = b.create_block();
        let done = b.create_block();
        let len = b.append_block_param(done, I64);
        let data = b.append_block_param(done, I64);
        let zero = b.ins().iconst(I64, 0);
        let none = [BlockArg::Value(zero), BlockArg::Value(zero)];
        let is_ptr = Self::is_ptr(b, x);
        b.ins().brif(is_ptr, obj, &[], done, &none);
        b.switch_to_block(obj);
        let info = b.ins().load(I64, flags(), x, 8);
        let kind = b.ins().band_imm_s(info, 0xff);
        let bytes = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_BYTES as i64);
        let array = b.ins().icmp_imm_s(IntCC::Equal, kind, checkers_rt::array::K_ARRAY as i64);
        let any = b.ins().bor(bytes, array);
        b.ins().brif(any, arr, &[], done, &none);
        b.switch_to_block(arr);
        let n = b.ins().load(I64, flags(), x, w::HDR as i32);
        let sh = b.ins().ishl_imm_s(n, 1);
        let n = b.ins().bor_imm_s(sh, 1);
        let elems = self.elements(b, x);
        let is_words = Self::is_word_array(b, info);
        let tagged = b.ins().bor_imm_s(elems, WORDS_BIT);
        let e = b.ins().select(is_words, tagged, zero);
        let d = b.ins().select(bytes, elems, e);
        b.ins().jump(done, &[BlockArg::Value(n), BlockArg::Value(d)]);
        b.switch_to_block(done);
        ArrayFacts { len, data }
    }

    /// Whether an object's header word `info` is an array's whose elements
    /// are words (`Layout::Words`: its tag).
    fn is_word_array(b: &mut FunctionBuilder, info: Value) -> Value {
        let mask = b.ins().iconst(I64, 0xffff_ffff_0000_00ffu64 as i64);
        let kt = b.ins().band(info, mask);
        let want = checkers_rt::array::K_ARRAY | (u64::from(checkers_rt::array::Layout::Words as u8) << 32);
        b.ins().icmp_imm_s(IntCC::Equal, kt, want as i64)
    }

    /// Where the elements of bytes or an array `x` are: after its header, or
    /// a slice points at them (#169).
    fn elements(&self, b: &mut FunctionBuilder, x: Value) -> Value {
        let ptr = b.ins().load(I64, flags(), x, (w::HDR + 8) as i32);
        let inline = b.ins().iadd_imm_s(x, (w::HDR + 16) as i64);
        let sliced = b.ins().icmp_imm_s(IntCC::NotEqual, ptr, 0);
        b.ins().select(sliced, ptr, inline)
    }

    /// In code compiled for the compiler, counts a function entry or a loop
    /// iteration against its work limit (`checkers_rt::prog::ck_tick`):
    /// every loop goes through one.
    fn tick(&mut self, b: &mut FunctionBuilder, st: &mut St) {
        if self.probe {
            self.rt_call(b, st, "ck_tick", &[]);
        }
    }

    fn fref(&mut self, b: &mut FunctionBuilder, st: &mut St, id: FuncId) -> FuncRef {
        if let Some(r) = st.frefs.get(&id) {
            return *r;
        }
        let r = self.m.declare_func_in_func(id, b.func);
        st.frefs.insert(id, r);
        r
    }

    fn addr(&mut self, b: &mut FunctionBuilder, st: &mut St, d: DataId) -> Value {
        let gv = match st.gvs.get(&d) {
            Some(g) => *g,
            None => {
                let g = self.m.declare_data_in_func(d, b.func);
                st.gvs.insert(d, g);
                g
            }
        };
        b.ins().symbol_value(I64, gv)
    }

    fn rt_call(&mut self, b: &mut FunctionBuilder, st: &mut St, name: &str, args: &[Value]) -> Option<Value> {
        let id = self.rt[name];
        let r = self.fref(b, st, id);
        let inst = b.ins().call(r, args);
        b.inst_results(inst).first().copied()
    }

    fn call1(&mut self, b: &mut FunctionBuilder, st: &mut St, name: &str, args: &[Value]) -> Value {
        self.rt_call(b, st, name, args).expect("a runtime function returning a word")
    }

    /// Words in a stack array; its address.
    fn array(&mut self, b: &mut FunctionBuilder, xs: &[Value]) -> Value {
        let ss = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, (8 * xs.len().max(1)) as u32, 3));
        for (k, x) in xs.iter().enumerate() {
            b.ins().stack_store(I64, *x, ss, (8 * k) as i32);
        }
        b.ins().stack_addr(I64, ss, 0)
    }

    fn call_array(&mut self, b: &mut FunctionBuilder, st: &mut St, sym: &str, xs: &[Value]) -> Value {
        let p = self.array(b, xs);
        let n = b.ins().iconst(I64, xs.len() as i64);
        self.call1(b, st, sym, &[p, n])
    }

    fn owner(&self, b: &mut FunctionBuilder, st: &St) -> Value {
        let o = if self.disasm.is_some() { 0 } else { st.owner };
        b.ins().iconst(I64, o as i64)
    }

    fn message(&mut self, b: &mut FunctionBuilder, st: &mut St, m: &str) -> (Value, Value) {
        let d = self.raw(m.as_bytes());
        let p = self.addr(b, st, d);
        let n = b.ins().iconst(I64, m.len() as i64);
        (p, n)
    }

    // ── reference counts (#567) ──────────────────────────────────────────────

    /// Is `x` a pointer, a non-zero multiple of 8? Rotated right by 3, its
    /// low bits become its top bits: it is then a number from 1 to 2^61 - 1.
    /// One condition, so a test moved out of a loop holds one register.
    fn is_ptr(b: &mut FunctionBuilder, x: Value) -> Value {
        let r = b.ins().rotr_imm_s(x, 3);
        let m = b.ins().iadd_imm_s(r, -1);
        b.ins().icmp_imm_s(IntCC::UnsignedLessThan, m, (1i64 << 61) - 1)
    }

    fn dup(&mut self, b: &mut FunctionBuilder, st: &mut St, x: Value) {
        // A constant word is never an object: objects are static data's
        // addresses, or allocated.
        if st.imm.contains(&x) || Self::const_word(b, x).is_some() || Self::small(b, st, x) {
            return;
        }
        let inc = b.create_block();
        let done = b.create_block();
        let c = Self::is_ptr(b, x);
        b.ins().brif(c, inc, &[], done, &[]);
        b.switch_to_block(inc);
        let one = b.ins().iconst(I64, 1);
        b.ins().atomic_rmw(I64, flags(), AtomicRmwOp::Add, x, one);
        b.ins().jump(done, &[]);
        b.switch_to_block(done);
    }

    fn drop_v(&mut self, b: &mut FunctionBuilder, st: &mut St, x: Value) {
        // A constant word is never an object: objects are static data's
        // addresses, or allocated.
        if st.imm.contains(&x) || Self::const_word(b, x).is_some() || Self::small(b, st, x) {
            return;
        }
        let dec = b.create_block();
        let free = b.create_block();
        let done = b.create_block();
        let c = Self::is_ptr(b, x);
        b.ins().brif(c, dec, &[], done, &[]);
        b.switch_to_block(dec);
        let one = b.ins().iconst(I64, 1);
        let old = b.ins().atomic_rmw(I64, flags(), AtomicRmwOp::Sub, x, one);
        let last = b.ins().icmp_imm_s(IntCC::Equal, old, 1);
        b.ins().brif(last, free, &[], done, &[]);
        b.switch_to_block(free);
        self.rt_call(b, st, "ck_free", &[x]);
        b.ins().jump(done, &[]);
        b.switch_to_block(done);
    }

    fn var(&self, _b: &mut FunctionBuilder, st: &St, v: V) -> Value {
        st.vars[v as usize].unwrap_or_else(|| panic!("native code uses variable {v} before defining it"))
    }

    // ── expressions ─────────────────────────────────────────────────────────

    /// Finish with `x`: return it, or pass it on. Where several words are
    /// expected, `x` is a failure's (it never returns): the rest are 0.
    fn finish(&mut self, b: &mut FunctionBuilder, st: &mut St, mode: &Mode, x: Value) {
        let n = match mode {
            Mode::Tail(n) => *n,
            Mode::Val(k) => b.func.dfg.num_block_params(*k),
            Mode::Join(_) => 1,
        };
        let mut xs = vec![x];
        if n > 1 {
            let z = b.ins().iconst(I64, 0);
            xs.resize(n, z);
        }
        self.finish_all(b, st, mode, &xs)
    }

    /// Finish with all of `xs`, the words expected.
    fn finish_all(&mut self, b: &mut FunctionBuilder, st: &mut St, mode: &Mode, xs: &[Value]) {
        match mode {
            Mode::Tail(_) => {
                b.ins().return_(xs);
            }
            Mode::Val(k) => {
                let args: Vec<BlockArg> = xs.iter().map(|x| BlockArg::Value(*x)).collect();
                b.ins().jump(*k, &args);
            }
            Mode::Join(j) => self.join_to(b, st, j, xs[0]),
        }
    }

    // ── joins matched at once (`Join`) ──────────────────────────────────────

    /// The `match` of `let x = a` in `body`, if `Join` applies: `body` is
    /// (after dropping `x`) a `match` on `x` whose arms are constructors
    /// without fields, and `a` branches.
    fn join_of<'a>(x: V, a: &E, body: &'a E) -> Option<(bool, &'a [Arm], Option<&'a E>)> {
        let (drop_x, m) = match body {
            E::Drop(v, m) if *v == x => (true, &**m),
            m => (false, m),
        };
        let E::Case { scrut, arms, lits, default } = m else { return None };
        let mut core = a;
        while let E::Let(_, _, e) | E::Dup(_, e) | E::Drop(_, e) | E::DropReuse(_, _, _, e) | E::At(_, e) = core {
            core = e;
        }
        let ok = *scrut == x && lits.is_empty() && !arms.is_empty() && arms.iter().all(|a| a.fields.is_empty()) && matches!(core, E::Case { .. });
        ok.then_some((drop_x, &arms[..], default.as_deref()))
    }

    /// The arm of `j` a constructor's word selects (`j.arms.len()`: the
    /// default).
    fn join_arm(&self, j: &Join, word: i64) -> usize {
        j.arms.iter().position(|a| w::nullary(a.con) as i64 == word).unwrap_or(j.arms.len())
    }

    /// How many of `e`'s branches end in each arm of `arms` (and the
    /// default, last): a constructor ends in its arm, a comparison in
    /// `True`'s and `False`'s.
    fn join_reach(&self, e: &E, arms: &[Arm], n: &mut [usize]) {
        let arm = |word: i64| arms.iter().position(|a| w::nullary(a.con) as i64 == word).unwrap_or(arms.len());
        match e {
            E::Let(_, _, e) | E::Dup(_, e) | E::Drop(_, e) | E::DropReuse(_, _, _, e) | E::At(_, e) => self.join_reach(e, arms, n),
            E::Case { arms: cs, lits, default, .. } => {
                for c in cs {
                    self.join_reach(&c.body, arms, n);
                }
                for (_, c) in lits {
                    self.join_reach(c, arms, n);
                }
                if let Some(d) = default {
                    self.join_reach(d, arms, n);
                }
            }
            E::Con { con, fields, reuse: None } if fields.is_empty() => n[arm(w::nullary(*con) as i64)] += 1,
            E::Borrow { op: BOp::Prim(Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge, _), .. } => {
                n[arm(self.true_w)] += 1;
                n[arm(self.false_w)] += 1;
            }
            _ => {}
        }
    }

    /// `let x = a` then `j`'s `match` on `x`.
    fn join(&mut self, b: &mut FunctionBuilder, st: &mut St, j: &Join, a: &E) {
        let n = j.arms.len() + 1;
        *j.state.borrow_mut() = JoinState { inline: vec![false; n], blocks: vec![None; n], other: None };
        self.emit(b, st, a, Mode::Join(j));
        // Any other value: matched.
        let other = j.state.borrow().other;
        if let Some(k) = other {
            b.switch_to_block(k);
            let r = b.block_params(k)[0];
            for idx in 0..j.arms.len() {
                let next = b.create_block();
                let c = b.ins().icmp_imm_s(IntCC::Equal, r, w::nullary(j.arms[idx].con) as i64);
                let to = self.join_block(b, j, idx);
                b.ins().brif(c, to, &[BlockArg::Value(r)], next, &[]);
                b.switch_to_block(next);
            }
            let to = self.join_block(b, j, j.arms.len());
            b.ins().jump(to, &[BlockArg::Value(r)]);
        }
        // The arms reached from several places, each once.
        for idx in 0..n {
            let blk = j.state.borrow().blocks[idx];
            if let Some(k) = blk {
                b.switch_to_block(k);
                st.quots.clone_from(&j.quots);
                let r = b.block_params(k)[0];
                self.join_arm_body(b, st, j, idx, r);
            }
        }
        st.quots.clone_from(&j.quots);
    }

    /// The block of arm `idx` of `j`, taking `x`'s word.
    fn join_block(&self, b: &mut FunctionBuilder, j: &Join, idx: usize) -> ir::Block {
        let mut s = j.state.borrow_mut();
        *s.blocks[idx].get_or_insert_with(|| {
            let k = b.create_block();
            b.append_block_param(k, I64);
            k
        })
    }

    /// Arm `idx` of `j`, `x` being `r`.
    fn join_arm_body(&mut self, b: &mut FunctionBuilder, st: &mut St, j: &Join, idx: usize, r: Value) {
        // An arm's constructor is its word: never dropped, known where the
        // arm uses it.
        let x = if idx < j.arms.len() {
            let x = b.ins().iconst(I64, w::nullary(j.arms[idx].con) as i64);
            st.imm.insert(x);
            x
        } else {
            if j.drop_x {
                self.drop_v(b, st, r);
            }
            r
        };
        st.vars[j.x as usize] = Some(x);
        match j.arms.get(idx).map(|a| &a.body).or(j.default) {
            Some(e) => self.emit(b, st, e, j.outer),
            None => {
                let o = self.owner(b, st);
                let v = self.call1(b, st, "ck_nomatch", &[x, o]);
                self.finish(b, st, &j.outer, v);
            }
        }
    }

    /// Go on to arm `idx` of `j` from here, `x` being `r`: the arm emitted
    /// here if this is the one place it is reached from, else its block.
    fn join_go(&mut self, b: &mut FunctionBuilder, st: &mut St, j: &Join, idx: usize, r: Value) {
        let here = j.reach[idx] == 1 && !std::mem::replace(&mut j.state.borrow_mut().inline[idx], true);
        if here {
            self.join_arm_body(b, st, j, idx, r);
        } else {
            let k = self.join_block(b, j, idx);
            b.ins().jump(k, &[BlockArg::Value(r)]);
        }
    }

    /// `a`'s value `x`, for `j`'s `match`.
    fn join_to(&mut self, b: &mut FunctionBuilder, st: &mut St, j: &Join, x: Value) {
        if let Some(word) = Self::const_word(b, x) {
            let idx = self.join_arm(j, word);
            return self.join_go(b, st, j, idx, x);
        }
        if let Some(cond) = st.conds.get(&x).cloned() {
            let blocks = [b.create_block(), b.create_block()];
            b.ins().brif(cond.c, blocks[0], &[], blocks[1], &[]);
            let quots = st.quots.clone();
            for (k, blk) in blocks.into_iter().enumerate() {
                b.switch_to_block(blk);
                st.quots.clone_from(&quots);
                let word = if k == 0 { self.true_w } else { self.false_w };
                let r = b.ins().iconst(I64, word);
                let facts = Self::assume_cond(b, st, &cond, k);
                let idx = self.join_arm(j, word);
                self.join_go(b, st, j, idx, r);
                Self::forget_cond(st, facts);
            }
            return;
        }
        let k = *j.state.borrow_mut().other.get_or_insert_with(|| {
            let k = b.create_block();
            b.append_block_param(k, I64);
            k
        });
        b.ins().jump(k, &[BlockArg::Value(x)]);
    }

    /// What holds where `cond` is true (`side` 0) or false (1): small
    /// integers, and the bounds its comparison gives its operands. To
    /// `forget_cond` once that code has been emitted.
    fn assume_cond(b: &FunctionBuilder, st: &mut St, cond: &Cond, side: usize) -> (Vec<Value>, Vec<(Value, Option<Range>)>) {
        let small = Self::assume_small(st, &cond.small_if[side]);
        let mut saved = Vec::new();
        if let Some((p, x, y)) = cond.rel {
            // The comparison that holds on this side, as `x op y`.
            let p = if side == 0 {
                p
            } else {
                match p {
                    Op::Eq => Op::Ne,
                    Op::Ne => Op::Eq,
                    Op::Lt => Op::Ge,
                    Op::Ge => Op::Lt,
                    Op::Le => Op::Gt,
                    _ => Op::Le,
                }
            };
            // `x > y` is `y < x`.
            let (p, x, y) = match p {
                Op::Gt => (Op::Lt, y, x),
                Op::Ge => (Op::Le, y, x),
                p => (p, x, y),
            };
            let (rx, ry) = (Self::range(b, st, x), Self::range(b, st, y));
            let below = |r: Range, d: i128| Range { lo: None, hi: r.hi.and_then(|h| h.checked_sub(d)) };
            let above = |r: Range, d: i128| Range { lo: r.lo.and_then(|l| l.checked_add(d)), hi: None };
            let (nx, ny) = match p {
                Op::Eq => (rx.meet(ry), ry.meet(rx)),
                Op::Lt => (rx.meet(below(ry, 1)), ry.meet(above(rx, 1))),
                Op::Le => (rx.meet(below(ry, 0)), ry.meet(above(rx, 0))),
                _ => (rx, ry),
            };
            for (v, new, old) in [(x, nx, rx), (y, ny, ry)] {
                if new != old && Self::const_word(b, v).is_none() {
                    saved.push((v, st.bounds.get(&v).copied()));
                    st.bounds.insert(v, new);
                }
            }
        }
        (small, saved)
    }

    fn forget_cond(st: &mut St, (small, saved): (Vec<Value>, Vec<(Value, Option<Range>)>)) {
        Self::forget(st, small);
        for (v, old) in saved.into_iter().rev() {
            match old {
                Some(r) => st.bounds.insert(v, r),
                None => st.bounds.remove(&v),
            };
        }
    }

    /// The value of `e`, in a fresh continuation.
    fn val(&mut self, b: &mut FunctionBuilder, st: &mut St, e: &E) -> Value {
        match e {
            E::Var(v) => self.var(b, st, *v),
            E::Int(n) => b.ins().iconst(I64, w::mk_int(*n) as i64),
            E::Erased => b.ins().iconst(I64, 0),
            E::Unit => b.ins().iconst(I64, w::UNIT as i64),
            E::Con { con, fields, reuse: None } if fields.is_empty() => b.ins().iconst(I64, w::nullary(*con) as i64),
            E::Str(s) => {
                let d = self.lit(w::K_BYTES, s.as_bytes());
                self.addr(b, st, d)
            }
            E::Bytes(x) => {
                let d = self.lit(w::K_BYTES, x);
                self.addr(b, st, d)
            }
            E::Static(v, id) => match self.statik(v, *id) {
                Placed::Word(x) => b.ins().iconst(I64, x as i64),
                Placed::Data(d, 0) => self.addr(b, st, d),
                Placed::Data(d, o) => {
                    let p = self.addr(b, st, d);
                    b.ins().iadd_imm_s(p, o as i64)
                }
            },
            // In the current block: a comparison's `Bool` is then the value
            // a `match` on it finds in `St::conds`, and a value known to be
            // a small integer is known to be one where it is used. So is
            // the value of code that doesn't branch around one: `let`s,
            // `dup`s and `drop`s before it, and `at`.
            E::Borrow { op, args, drops } => self.borrow_e(b, st, *op, args, drops),
            E::Let(x, a, body) => {
                self.bind(b, st, *x, a);
                self.val(b, st, body)
            }
            // Code of another definition: the same code, whose runtime
            // errors name that definition.
            E::At(o, x) => {
                let saved = std::mem::replace(&mut st.owner, *o);
                let v = self.val(b, st, x);
                st.owner = saved;
                v
            }
            E::Dup(v, body) => {
                let x = self.var(b, st, *v);
                self.dup(b, st, x);
                self.val(b, st, body)
            }
            E::Drop(v, body) => {
                let x = self.var(b, st, *v);
                self.drop_v(b, st, x);
                self.val(b, st, body)
            }
            E::DropReuse(v, tok, n, body) => {
                let x = self.var(b, st, *v);
                let t = self.drop_reuse(b, st, x, *n);
                st.vars[*tok as usize] = Some(t);
                self.val(b, st, body)
            }
            _ => {
                let k = b.create_block();
                let r = b.append_block_param(k, I64);
                self.emit(b, st, e, Mode::Val(k));
                b.switch_to_block(k);
                r
            }
        }
    }

    /// `x` bound to the value of `a`.
    fn bind(&mut self, b: &mut FunctionBuilder, st: &mut St, x: V, a: &E) {
        let v = self.val(b, st, a);
        if Self::immediate(a) {
            st.imm.insert(v);
        }
        st.vars[x as usize] = Some(v);
    }

    fn emit(&mut self, b: &mut FunctionBuilder, st: &mut St, e: &E, mode: Mode) {
        match e {
            E::Var(_) | E::Int(_) | E::Erased | E::Unit | E::Str(_) | E::Bytes(_) | E::Static(..) => {
                let x = self.val(b, st, e);
                self.finish(b, st, &mode, x)
            }
            E::Global(d) => {
                let x = self.global(b, st, *d);
                self.finish(b, st, &mode, x)
            }
            E::ConFn(c) => {
                let f = self.p.con_wraps[c];
                let d = self.closure(f);
                let x = self.addr(b, st, d);
                self.finish(b, st, &mode, x)
            }
            E::Let(x, a, body) => {
                if let Some((drop_x, arms, default)) = Self::join_of(*x, a, body) {
                    let mut reach = vec![0; arms.len() + 1];
                    self.join_reach(a, arms, &mut reach);
                    let j = Join { x: *x, drop_x, arms, default, outer: mode, reach, state: Default::default(), quots: st.quots.clone() };
                    return self.join(b, st, &j, a);
                }
                self.bind(b, st, *x, a);
                self.emit(b, st, body, mode)
            }
            E::Call { f, args, .. } => {
                let mut vs = vec![b.ins().iconst(I64, 0)];
                for a in args {
                    vs.push(self.val(b, st, a));
                }
                let r = self.fref(b, st, self.funcs[*f as usize]);
                match mode {
                    Mode::Tail(_) if st.this.is_some_and(|(i, _)| i == *f) => {
                        let top = st.this.unwrap().1;
                        let args: Vec<BlockArg> = vs.iter().map(|v| BlockArg::Value(*v)).collect();
                        b.ins().jump(top, &args);
                    }
                    Mode::Tail(_) => {
                        b.ins().return_call(r, &vs);
                    }
                    Mode::Val(_) | Mode::Join(_) => {
                        let inst = b.ins().call(r, &vs);
                        let xs = b.inst_results(inst).to_vec();
                        self.finish_all(b, st, &mode, &xs);
                    }
                }
            }
            E::Apply { f, args, .. } => {
                let fv = self.val(b, st, f);
                let vs: Vec<Value> = args.iter().map(|a| self.val(b, st, a)).collect();
                self.apply(b, st, fv, &vs, mode)
            }
            E::MkClo { f, captured } => {
                let n = captured.len();
                let f = &self.p.entries.get(f).copied().unwrap_or(*f);
                assert!(!self.p.borrowed.contains_key(f), "a closure of `{}`, which borrows parameters", self.p.funcs[*f as usize].name);
                let arity = arity_of(&self.p.funcs[*f as usize]) as u64;
                let x = self.alloc(b, st, w::info(w::K_CLO, n as u64, arity), w::HDR + 8 + 8 * n);
                let r = self.fref(b, st, self.funcs[*f as usize]);
                let code = b.ins().func_addr(I64, r);
                b.ins().store(flags(), code, x, w::HDR as i32);
                for (k, c) in captured.iter().enumerate() {
                    let cv = self.var(b, st, *c);
                    b.ins().store(flags(), cv, x, (w::HDR + 8 + 8 * k) as i32);
                }
                self.finish(b, st, &mode, x)
            }
            E::Con { con, fields, reuse } => {
                let vs: Vec<Value> = fields.iter().map(|a| self.val(b, st, a)).collect();
                let tok = reuse.map(|t| self.var(b, st, t));
                let x = self.build_con(b, st, *con, &vs, tok);
                self.finish(b, st, &mode, x)
            }
            E::Multi(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                self.finish_all(b, st, &mode, &vs)
            }
            E::LetMulti(xs, a, body) => {
                let k = b.create_block();
                let vs: Vec<Value> = xs.iter().map(|_| b.append_block_param(k, I64)).collect();
                self.emit(b, st, a, Mode::Val(k));
                b.switch_to_block(k);
                for (x, v) in xs.iter().zip(vs) {
                    st.vars[*x as usize] = Some(v);
                }
                self.emit(b, st, body, mode)
            }
            E::Tuple(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                let x = self.alloc(b, st, w::info(w::K_TUPLE, vs.len() as u64, 0), w::HDR + 8 * vs.len());
                for (k, v) in vs.iter().enumerate() {
                    b.ins().store(flags(), *v, x, (w::HDR + 8 * k) as i32);
                }
                let x = self.flatten_tuple(b, st, x, vs[vs.len() - 1]);
                self.finish(b, st, &mode, x)
            }
            E::Borrow { op, args, drops } => {
                let x = self.borrow_e(b, st, *op, args, drops);
                self.finish(b, st, &mode, x)
            }
            E::Par(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                let x = self.call_array(b, st, "ck_par", &vs);
                self.finish(b, st, &mode, x)
            }
            E::At(o, x) => {
                let saved = std::mem::replace(&mut st.owner, *o);
                self.emit(b, st, x, mode);
                st.owner = saved;
            }
            E::Fail(m) => {
                let o = self.owner(b, st);
                let (p, n) = self.message(b, st, m);
                let x = self.call1(b, st, "ck_fail", &[o, p, n]);
                self.finish(b, st, &mode, x)
            }
            E::Dup(v, body) => {
                let x = self.var(b, st, *v);
                self.dup(b, st, x);
                self.emit(b, st, body, mode)
            }
            E::Drop(v, body) => {
                let x = self.var(b, st, *v);
                self.drop_v(b, st, x);
                self.emit(b, st, body, mode)
            }
            E::DropReuse(v, tok, n, body) => {
                let x = self.var(b, st, *v);
                let t = self.drop_reuse(b, st, x, *n);
                st.vars[*tok as usize] = Some(t);
                self.emit(b, st, body, mode)
            }
            E::Case { scrut, arms, lits, default } => self.case(b, st, *scrut, arms, lits, default.as_deref(), mode),
        }
    }

    /// `op args`, then `drops` dropped.
    fn borrow_e(&mut self, b: &mut FunctionBuilder, st: &mut St, op: BOp, args: &[E], drops: &[V]) -> Value {
        let vs: Vec<Value> = args.iter().map(|a| self.val(b, st, a)).collect();
        if let (BOp::Prim(Op::Concat, _), Some(given)) = (op, Self::gives_left(args, drops)) {
            // The last use of the left side: `++` takes it, so a string
            // or array no one else holds is appended to in place.
            let x = self.call1(b, st, "ck_concat_own", &[vs[0], vs[1]]);
            for d in drops.iter().filter(|d| **d != given) {
                let dv = self.var(b, st, *d);
                self.drop_v(b, st, dv);
            }
            return x;
        }
        let mut ds: Vec<Value> = drops.iter().map(|d| self.var(b, st, *d)).collect();
        let x = match op {
            // Integer operations drop their operands on each path: on the
            // fast path they are small integers, so there is nothing to do.
            BOp::Prim(p, nat) => {
                let mine = Self::take_args(&vs, &mut ds);
                let key = match args {
                    [x, y] => Atom::of(x).zip(Atom::of(y)),
                    _ => None,
                };
                self.prim(b, st, p, nat, &vs, &mine, key)
            }
            op => self.borrow(b, st, op, &vs),
        };
        for d in ds {
            self.drop_v(b, st, d);
        }
        x
    }

    /// The values of `drops` that are among `args`, taken out of `drops`.
    fn take_args(args: &[Value], drops: &mut Vec<Value>) -> Vec<Value> {
        let mut mine = Vec::new();
        drops.retain(|d| {
            let arg = args.contains(d);
            if arg {
                mine.push(*d);
            }
            !arg
        });
        mine
    }

    fn alloc(&mut self, b: &mut FunctionBuilder, st: &mut St, info: u64, size: usize) -> Value {
        let i = b.ins().iconst(I64, info as i64);
        let s = b.ins().iconst(I64, size as i64);
        self.call1(b, st, "ck_alloc", &[i, s])
    }

    /// A constructor value; with `tok` (reused memory, or 0) build in place.
    fn build_con(&mut self, b: &mut FunctionBuilder, st: &mut St, con: u32, fields: &[Value], tok: Option<Value>) -> Value {
        if fields.is_empty() {
            return b.ins().iconst(I64, w::nullary(con) as i64);
        }
        let info = w::info(w::K_CON, fields.len() as u64, con as u64);
        let size = w::HDR + 8 * fields.len();
        let x = match tok {
            None => self.alloc(b, st, info, size),
            Some(t) => {
                let fresh = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                b.ins().brif(t, done, &[BlockArg::Value(t)], fresh, &[]);
                b.switch_to_block(fresh);
                let a = self.alloc(b, st, info, size);
                b.ins().jump(done, &[BlockArg::Value(a)]);
                b.switch_to_block(done);
                let iv = b.ins().iconst(I64, info as i64);
                b.ins().store(flags(), iv, r, 8);
                r
            }
        };
        for (k, v) in fields.iter().enumerate() {
            b.ins().store(flags(), *v, x, (w::HDR + 8 * k) as i32);
        }
        x
    }

    /// Drop `x` (`n` fields); its memory if it was the only reference, else 0.
    fn drop_reuse(&mut self, b: &mut FunctionBuilder, st: &mut St, x: Value, n: usize) -> Value {
        let check = b.create_block();
        let mine = b.create_block();
        let shared = b.create_block();
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
        let c = Self::is_ptr(b, x);
        b.ins().brif(c, check, &[], shared, &[]);
        b.switch_to_block(check);
        let rc = b.ins().atomic_load(I64, flags(), x);
        let one = b.ins().icmp_imm_s(IntCC::Equal, rc, 1);
        b.ins().brif(one, mine, &[], shared, &[]);
        b.switch_to_block(mine);
        let zero = b.ins().iconst(I64, 0);
        for k in 0..n {
            let f = b.ins().load(I64, flags(), x, (w::HDR + 8 * k) as i32);
            self.drop_v(b, st, f);
            b.ins().store(flags(), zero, x, (w::HDR + 8 * k) as i32);
        }
        b.ins().jump(done, &[BlockArg::Value(x)]);
        b.switch_to_block(shared);
        self.drop_v(b, st, x);
        let z = b.ins().iconst(I64, 0);
        b.ins().jump(done, &[BlockArg::Value(z)]);
        b.switch_to_block(done);
        r
    }

    fn global(&mut self, b: &mut FunctionBuilder, st: &mut St, d: u32) -> Value {
        match self.p.defs.get(&d).cloned() {
            Some(DefShape::Fn { func, .. }) => {
                let c = self.closure(func);
                self.addr(b, st, c)
            }
            Some(DefShape::Builtin { wrap, .. }) => {
                let c = self.closure(wrap);
                self.addr(b, st, c)
            }
            Some(DefShape::Caf { func }) => {
                let s = self.slot(d);
                let sp = self.addr(b, st, s);
                let v = b.ins().atomic_load(I64, flags(), sp);
                let unset = b.ins().icmp_imm_s(IntCC::Equal, v, w::UNSET as i64);
                let init = b.create_block();
                let have = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                b.ins().brif(unset, init, &[], have, &[]);
                b.switch_to_block(init);
                let fr = self.fref(b, st, self.funcs[func as usize]);
                let code = b.ins().func_addr(I64, fr);
                let x = self.call1(b, st, "ck_caf", &[sp, code]);
                b.ins().jump(done, &[BlockArg::Value(x)]);
                b.switch_to_block(have);
                self.dup(b, st, v);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(done);
                r
            }
            Some(DefShape::Missing(_)) | None => {
                let o = self.owner(b, st);
                let msg = format!("`{}` has no implementation in this interpreter yet", self.missing_name(d));
                let (p, n) = self.message(b, st, &msg);
                self.call1(b, st, "ck_error", &[o, p, n])
            }
        }
    }

    fn missing_name(&self, d: u32) -> String {
        match self.p.defs.get(&d) {
            Some(DefShape::Missing(n)) => n.clone(),
            _ => {
                let i = &self.g.defs[d as usize];
                format!("{}.{}", i.module, i.name)
            }
        }
    }

    /// `f a1 … an`: through the code pointer if `f` is a closure taking
    /// exactly `n` arguments, else through the runtime.
    fn apply(&mut self, b: &mut FunctionBuilder, st: &mut St, f: Value, args: &[Value], mode: Mode) {
        let n = args.len();
        let check = b.create_block();
        let fast = b.create_block();
        let slow = b.create_block();
        let c = Self::is_ptr(b, f);
        b.ins().brif(c, check, &[], slow, &[]);
        b.switch_to_block(check);
        let info = b.ins().load(I64, flags(), f, 8);
        let want = b.ins().iconst(I64, w::info(w::K_CLO, 0, n as u64) as i64);
        // Kind and arity, ignoring the free-variable count.
        let mask = b.ins().iconst(I64, (0xffff_ffff_0000_00ffu64) as i64);
        let got = b.ins().band(info, mask);
        let ok = b.ins().icmp(IntCC::Equal, got, want);
        b.ins().brif(ok, fast, &[], slow, &[]);
        b.switch_to_block(fast);
        let code = b.ins().load(I64, flags(), f, w::HDR as i32);
        let sig = b.import_signature(tail_sig(n));
        let mut vs = vec![f];
        vs.extend_from_slice(args);
        match mode {
            Mode::Tail(n) => {
                debug_assert_eq!(n, 1, "a closure returns one word");
                b.ins().return_call_indirect(sig, code, &vs);
            }
            Mode::Val(_) | Mode::Join(_) => {
                let inst = b.ins().call_indirect(sig, code, &vs);
                let x = b.inst_results(inst)[0];
                self.finish(b, st, &mode, x);
            }
        }
        b.switch_to_block(slow);
        let p = self.array(b, args);
        let nn = b.ins().iconst(I64, n as i64);
        let x = self.call1(b, st, "ck_apply", &[f, p, nn]);
        self.finish(b, st, &mode, x);
    }

    fn bool_of(&self, b: &mut FunctionBuilder, c: Value) -> Value {
        let t = b.ins().iconst(I64, self.true_w);
        let f = b.ins().iconst(I64, self.false_w);
        b.ins().select(c, t, f)
    }

    /// A comparison's `Bool` from its condition, which a `match` on it
    /// branches on instead (`St::conds`).
    fn bool_cond(&self, b: &mut FunctionBuilder, st: &mut St, c: Value, small_if: [Vec<Value>; 2], rel: (Op, Value, Value)) -> Value {
        let w = self.bool_of(b, c);
        st.conds.insert(w, Cond { c, small_if, rel: Some(rel) });
        w
    }

    /// `a ++ b` whose left side is a variable this is the last use of (it
    /// would be dropped right after), and not also the right side: that
    /// variable, which `++` may then take.
    fn gives_left(args: &[E], drops: &[V]) -> Option<V> {
        match args {
            [E::Var(v), y] if drops.iter().filter(|d| *d == v).count() == 1 && !matches!(y, E::Var(u) if u == v) => Some(*v),
            _ => None,
        }
    }

    /// Is `e`'s value never a pointer? A comparison gives `True` or `False`,
    /// constructors without fields; so does a `match` whose arms each give
    /// one (`a and b`).
    fn immediate(e: &E) -> bool {
        match e {
            E::Let(_, _, x) | E::At(_, x) | E::Dup(_, x) | E::Drop(_, x) | E::DropReuse(_, _, _, x) => Self::immediate(x),
            E::Con { fields, reuse: None, .. } => fields.is_empty(),
            E::Case { arms, lits, default, .. } => {
                arms.iter().all(|a| Self::immediate(&a.body)) && lits.iter().all(|(_, e)| Self::immediate(e)) && default.as_deref().is_none_or(Self::immediate)
            }
            _ => matches!(e, E::Borrow { op: BOp::Prim(Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge, _), .. }),
        }
    }

    // ── small integers ──────────────────────────────────────────────────────

    /// The word `x` is, if it is a constant.
    fn const_word(b: &FunctionBuilder, x: Value) -> Option<i64> {
        let ValueDef::Result(inst, _) = b.func.dfg.value_def(x) else { return None };
        match b.func.dfg.insts[inst] {
            InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => Some(imm.bits()),
            _ => None,
        }
    }

    /// Is `x` known to be a small integer where code is being emitted: a
    /// constant one (only integers' words are odd), or a fact in `St::ints`?
    fn small(b: &FunctionBuilder, st: &St, x: Value) -> bool {
        st.ints.contains(&x) || Self::const_word(b, x).is_some_and(|w| w & 1 == 1) || SMALL.holds(Self::range(b, st, x))
    }

    /// The constant bounds known of integer `x`: a constant's own, else
    /// `St::bounds`.
    fn range(b: &FunctionBuilder, st: &St, x: Value) -> Range {
        match Self::const_word(b, x) {
            Some(w) if w & 1 == 1 => Range::exact((w >> 1) as i128),
            _ => st.bounds.get(&x).copied().unwrap_or(Range::ANY),
        }
    }

    /// The bounds of `p` on `a`, if it is an integer operation.
    fn op_range(b: &FunctionBuilder, st: &St, p: Op, nat: bool, a: &[Value]) -> Option<Range> {
        let r = |k: usize| Self::range(b, st, a[k]);
        let prim = match p {
            Op::Add => Prim::Add,
            Op::Sub => Prim::Sub,
            Op::Mul => Prim::Mul,
            Op::Div => Prim::Div,
            Op::Rem => Prim::Rem,
            Op::Neg => {
                let x = r(0);
                return Some(Range { lo: x.hi.and_then(i128::checked_neg), hi: x.lo.and_then(i128::checked_neg) });
            }
            // An `Array U8`'s element: a byte.
            Op::Index if nat => return Some(Range { lo: Some(0), hi: Some(255) }),
            // A length is a small integer, and not negative.
            Op::Len => return Some(Range { lo: Some(0), hi: SMALL.hi }),
            _ => return None,
        };
        Some(crate::range::combine(prim, r(0), r(1), nat && p == Op::Sub))
    }

    /// Take `xs` to be small integers; those that weren't known, to `forget`
    /// once the code where they are has been emitted.
    fn assume_small(st: &mut St, xs: &[Value]) -> Vec<Value> {
        xs.iter().copied().filter(|x| st.ints.insert(*x)).collect()
    }

    fn forget(st: &mut St, added: Vec<Value>) {
        for x in added {
            st.ints.remove(&x);
        }
    }

    /// Go on to `yes` if all of `xs` are small integers, else to `no`. Only
    /// the words not already known to be are tested.
    fn if_small(b: &mut FunctionBuilder, st: &St, xs: &[Value], yes: ir::Block, no: ir::Block) {
        let mut unknown: Vec<Value> = Vec::new();
        for x in xs {
            if !Self::small(b, st, *x) && !unknown.contains(x) {
                unknown.push(*x);
            }
        }
        let Some((first, rest)) = unknown.split_first() else {
            b.ins().jump(yes, &[]);
            return;
        };
        let all = rest.iter().fold(*first, |a, x| b.ins().band(a, *x));
        let t = b.ins().band_imm_s(all, 1);
        b.ins().brif(t, yes, &[], no, &[]);
    }

    /// The 128-bit value of number `x`, if it is a small integer or a
    /// two-word object; else on to `no`. With `any`, `x` may be any value,
    /// not only a number.
    fn wide_of(b: &mut FunctionBuilder, st: &St, x: Value, any: bool, no: ir::Block) -> Value {
        if Self::small(b, st, x) {
            let n = b.ins().sshr_imm_s(x, 1);
            return wide::of_i64(b, n);
        }
        let int = b.create_block();
        let obj = b.create_block();
        let load = b.create_block();
        let done = b.create_block();
        let r = b.append_block_param(done, I128);
        let t = b.ins().band_imm_s(x, 1);
        b.ins().brif(t, int, &[], obj, &[]);
        b.switch_to_block(int);
        let n = b.ins().sshr_imm_s(x, 1);
        let n = wide::of_i64(b, n);
        b.ins().jump(done, &[BlockArg::Value(n)]);
        b.switch_to_block(obj);
        if any {
            let header = b.create_block();
            let ptr = Self::is_ptr(b, x);
            b.ins().brif(ptr, header, &[], no, &[]);
            b.switch_to_block(header);
        }
        let info = b.ins().load(I64, flags(), x, 8);
        let two_words = b.ins().icmp_imm_s(IntCC::Equal, info, checkers_rt::obj::INFO_I128 as i64);
        b.ins().brif(two_words, load, &[], no, &[]);
        b.switch_to_block(load);
        let lo = b.ins().load(I64, flags(), x, w::HDR as i32);
        let hi = b.ins().load(I64, flags(), x, w::HDR as i32 + 8);
        let n = b.ins().iconcat(lo, hi);
        b.ins().jump(done, &[BlockArg::Value(n)]);
        b.switch_to_block(done);
        r
    }

    /// A call of `w`'s function on `xs`: its results.
    fn call_wide(&mut self, b: &mut FunctionBuilder, st: &mut St, w: Wide, xs: &[Value]) -> Vec<Value> {
        let id = match self.wides.get(&w) {
            Some(id) => *id,
            None => {
                let id = self.m.declare_function(w.name(), Linkage::Local, &w.sig()).expect("declare a 128-bit function");
                self.wides.insert(w, id);
                id
            }
        };
        let r = self.fref(b, st, id);
        let inst = b.ins().call(r, xs);
        b.inst_results(inst).to_vec()
    }

    /// `w`'s function: the operation on two numbers (one for `Neg`)
    /// borrowed, and the owner of its runtime errors where it has them; on
    /// 128 bits, or by the runtime where they or the result aren't within
    /// them. `Cmp` gives -1, 0 or 1, and `Eq` 1 for equal, else 0.
    fn define_wide(&mut self, fctx: &mut FunctionBuilderContext, ctx: &mut cranelift_codegen::Context, w: Wide) {
        ctx.func.signature = w.sig();
        ctx.func.name = ir::UserFuncName::user(1, w as u32);
        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, fctx);
            let b = &mut builder;
            let mut st = St::new(Vec::new(), 0, HashSet::new());
            let st = &mut st;
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let xs = b.block_params(entry).to_vec();
            let no = b.create_block();
            b.set_cold_block(no);
            let operands = if w == Wide::Neg { 1 } else { 2 };
            let ns: Vec<Value> = xs[..operands].iter().map(|x| Self::wide_of(b, st, *x, w == Wide::Eq, no)).collect();
            // The value, unless `over`.
            let mut finish = |me: &mut Self, b: &mut FunctionBuilder, v: Value, over: Value| {
                let fine = b.create_block();
                b.ins().brif(over, no, &[], fine, &[]);
                b.switch_to_block(fine);
                let v = me.box_wide(b, st, v);
                b.ins().return_(&[v]);
            };
            match w {
                Wide::Add => {
                    let (v, o) = b.ins().sadd_overflow(ns[0], ns[1]);
                    finish(self, b, v, o)
                }
                Wide::Sub => {
                    let (v, o) = b.ins().ssub_overflow(ns[0], ns[1]);
                    finish(self, b, v, o)
                }
                Wide::Mul => {
                    let (v, o) = wide::mul(b, ns[0], ns[1]);
                    finish(self, b, v, o)
                }
                Wide::Neg => {
                    let zero = wide::zero(b);
                    let (v, o) = b.ins().ssub_overflow(zero, ns[0]);
                    finish(self, b, v, o)
                }
                // `Nat`s: below zero is the runtime's to report.
                Wide::NatSub => {
                    let below = b.ins().icmp(IntCC::SignedLessThan, ns[0], ns[1]);
                    let v = b.ins().isub(ns[0], ns[1]);
                    finish(self, b, v, below)
                }
                Wide::Cmp => {
                    let gt = b.ins().icmp(IntCC::SignedGreaterThan, ns[0], ns[1]);
                    let lt = b.ins().icmp(IntCC::SignedLessThan, ns[0], ns[1]);
                    let gt = b.ins().uextend(I64, gt);
                    let lt = b.ins().uextend(I64, lt);
                    let order = b.ins().isub(gt, lt);
                    b.ins().return_(&[order]);
                }
                Wide::Eq => {
                    let e = b.ins().icmp(IntCC::Equal, ns[0], ns[1]);
                    let e = b.ins().uextend(I64, e);
                    b.ins().return_(&[e]);
                }
                // The result, and the other as a small integer's word, or 0
                // (past a word, or a quotient past 128 bits, `-2^127 / -1`).
                // Division by zero is the runtime's to report.
                Wide::Div | Wide::Rem => {
                    let zero = wide::zero(b);
                    let by_zero = b.ins().icmp(IntCC::Equal, ns[1], zero);
                    let divide = b.create_block();
                    b.ins().brif(by_zero, no, &[], divide, &[]);
                    b.switch_to_block(divide);
                    let (q, m, over) = wide::div_rem(b, ns[0], ns[1]);
                    let (v, o, fits) = if w == Wide::Rem {
                        let (fits, word) = wide::small_word(b, q);
                        let over = b.ins().bxor_imm_s(over, 1);
                        (m, word, b.ins().band(fits, over))
                    } else {
                        let fine = b.create_block();
                        b.ins().brif(over, no, &[], fine, &[]);
                        b.switch_to_block(fine);
                        let (fits, word) = wide::small_word(b, m);
                        (q, word, fits)
                    };
                    let zero = b.ins().iconst(I64, 0);
                    let o = b.ins().select(fits, o, zero);
                    let v = self.box_wide(b, st, v);
                    b.ins().return_(&[v, o]);
                }
            }
            b.switch_to_block(no);
            let rt = match w {
                Wide::Add => "ck_add",
                Wide::Sub => "ck_sub",
                Wide::Mul => "ck_mul",
                Wide::Neg => "ck_neg",
                Wide::NatSub => "ck_natsub",
                Wide::Cmp => "ck_cmp",
                Wide::Eq => "ck_eq",
                Wide::Div => "ck_div",
                Wide::Rem => "ck_rem",
            };
            let r = self.call1(b, st, rt, &xs);
            let r = if w == Wide::Eq {
                let e = b.ins().icmp_imm_s(IntCC::Equal, r, self.true_w);
                b.ins().uextend(I64, e)
            } else {
                r
            };
            // Past 128 bits, the other result of a division isn't given.
            let mut rets = vec![r];
            if matches!(w, Wide::Div | Wide::Rem) {
                rets.push(b.ins().iconst(I64, 0));
            }
            b.ins().return_(&rets);
            builder.seal_all_blocks();
            builder.finalize(self.m.isa().frontend_config());
        }
        ctx.set_disasm(self.disasm.is_some());
        if let Err(e) = self.m.define_function(self.wides[&w], ctx) {
            panic!("native code for `{}`: {e:?}", w.name());
        }
        if let Some(d) = &mut self.disasm {
            d.push((w.name().to_string(), named_code(&self.m, ctx)));
        }
        self.m.clear_context(ctx);
    }

    /// The number `x` (128 bits): a small integer if it fits in a word,
    /// else a new two-word object, as the runtime keeps numbers.
    fn box_wide(&mut self, b: &mut FunctionBuilder, st: &mut St, x: Value) -> Value {
        let (fits, word) = wide::small_word(b, x);
        let obj = b.create_block();
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
        b.ins().brif(fits, done, &[BlockArg::Value(word)], obj, &[]);
        b.switch_to_block(obj);
        let o = self.alloc(b, st, checkers_rt::obj::INFO_I128, w::HDR + 16);
        let (lo, hi) = b.ins().isplit(x);
        b.ins().store(flags(), lo, o, w::HDR as i32);
        b.ins().store(flags(), hi, o, w::HDR as i32 + 8);
        b.ins().jump(done, &[BlockArg::Value(o)]);
        b.switch_to_block(done);
        r
    }

    /// An integer operation on `xs`: `fast` (its value, still to be tagged
    /// with `+ 1` if `tag`, and whether it overflowed) if they are small
    /// integers and it doesn't overflow, else `wide`'s function (128 bits,
    /// or the runtime past them) on `xs`. The operands' `drops` are dropped
    /// off the fast path only: on it they are small integers. Where the
    /// operands' bounds show that they are small integers and the result
    /// one too (`fits`), only `fast` without its overflow check
    /// (`fast(b, false)`).
    #[allow(clippy::too_many_arguments)]
    fn arith(
        &mut self,
        b: &mut FunctionBuilder,
        st: &mut St,
        xs: &[Value],
        fits: bool,
        fast: impl FnOnce(&mut FunctionBuilder, bool) -> (Value, Option<Value>),
        tag: bool,
        wide: Wide,
        drops: &[Value],
    ) -> Value {
        if fits {
            let (v, _) = fast(b, false);
            return if tag { b.ins().iadd_imm_s(v, 1) } else { v };
        }
        let try_fast = b.create_block();
        let ok = b.create_block();
        let slow_b = b.create_block();
        b.set_cold_block(slow_b);
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
        Self::if_small(b, st, xs, try_fast, slow_b);
        b.switch_to_block(try_fast);
        let (v, overflow) = fast(b, true);
        let overflow = overflow.expect("a checked operation's overflow");
        b.ins().brif(overflow, slow_b, &[], ok, &[]);
        // The value's other uses are in a block of their own: on x86-64,
        // the one instruction setting the overflow flag (`imul`) then gives
        // the value too, rather than being repeated for it.
        b.switch_to_block(ok);
        let v = if tag { b.ins().iadd_imm_s(v, 1) } else { v };
        b.ins().jump(done, &[BlockArg::Value(v)]);
        b.switch_to_block(slow_b);
        let s = self.call_wide(b, st, wide, xs)[0];
        for d in drops {
            self.drop_v(b, st, *d);
        }
        b.ins().jump(done, &[BlockArg::Value(s)]);
        b.switch_to_block(done);
        r
    }

    /// Euclidean `/` or `%` (the remainder never negative) of `x` and `y`
    /// (`key`, if they are variables or constants). Where the other of the
    /// pair was emitted before, on its operands, it gave this one's result
    /// if that is a small integer; where the other comes after (`St::pairs`),
    /// this one gives it its result (`St::quots`).
    #[allow(clippy::too_many_arguments)]
    fn divide(&mut self, b: &mut FunctionBuilder, st: &mut St, rem: bool, x: Value, y: Value, owner: Value, drops: &[Value], fits: bool, key: Option<Pair>) -> Value {
        if let Some(q) = key.and_then(|k| st.quots.get(&k)).copied().filter(|q| q.rem == rem) {
            let have = b.create_block();
            let divide = b.create_block();
            let done = b.create_block();
            let r = b.append_block_param(done, I64);
            b.ins().brif(q.word, have, &[], divide, &[]);
            b.switch_to_block(have);
            for d in drops {
                self.drop_v(b, st, *d);
            }
            b.ins().jump(done, &[BlockArg::Value(q.word)]);
            b.switch_to_block(divide);
            let (v, _) = self.divide_now(b, st, rem, x, y, owner, drops, fits, false);
            b.ins().jump(done, &[BlockArg::Value(v)]);
            b.switch_to_block(done);
            if rem && Self::small(b, st, y) || fits {
                st.ints.insert(r);
            }
            return r;
        }
        let pair = key.filter(|k| st.pairs.contains(k));
        let (r, other) = self.divide_now(b, st, rem, x, y, owner, drops, fits, pair.is_some());
        if let (Some(k), Some(word)) = (pair, other) {
            st.quots.insert(k, Quot { rem: !rem, word });
        }
        r
    }

    /// `x / y` or `x % y`: inline when both are small integers and the
    /// divisor isn't zero; otherwise its 128-bit function (`Wide`), which
    /// goes to the runtime past 128 bits and for division by zero. With
    /// bounds showing that both are small integers, the divisor not zero
    /// and (for `/`) the result a small integer (`fits`), there is no other
    /// path. With `other`, also the other result as a small integer's word,
    /// or 0 (`Quot`).
    #[allow(clippy::too_many_arguments)]
    fn divide_now(
        &mut self,
        b: &mut FunctionBuilder,
        st: &mut St,
        rem: bool,
        x: Value,
        y: Value,
        owner: Value,
        drops: &[Value],
        fits: bool,
        other: bool,
    ) -> (Value, Option<Value>) {
        let ry = Self::range(b, st, y);
        // A proved program's divisor isn't zero (§13.3).
        let nonzero = self.g.proved || ry.lo.is_some_and(|l| l > 0) || ry.hi.is_some_and(|h| h < 0);
        if Self::small(b, st, x) && Self::small(b, st, y) && nonzero && (rem || fits) {
            let (v, o) = Self::divide_small(b, rem, x, y, None, other);
            return (v, o);
        }
        let slow = b.create_block();
        b.set_cold_block(slow);
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
        let other_param = other.then(|| b.append_block_param(done, I64));
        let jump_done = |b: &mut FunctionBuilder, v: Value, o: Option<Value>| {
            let mut args = vec![BlockArg::Value(v)];
            args.extend(o.map(BlockArg::Value));
            b.ins().jump(done, &args);
        };
        let check = b.create_block();
        let fast = b.create_block();
        Self::if_small(b, st, &[x, y], check, slow);
        b.switch_to_block(check);
        if nonzero {
            b.ins().jump(fast, &[]);
        } else {
            // The word for 0 is 1.
            let nonzero = b.ins().icmp_imm_s(IntCC::NotEqual, y, 1);
            b.ins().brif(nonzero, fast, &[], slow, &[]);
        }
        b.switch_to_block(fast);
        let (v, o) = Self::divide_small(b, rem, x, y, (!fits).then_some(slow), other);
        jump_done(b, v, o);
        // Within 128 bits, one division gives both results.
        b.switch_to_block(slow);
        let rs = self.call_wide(b, st, if rem { Wide::Rem } else { Wide::Div }, &[x, y, owner]);
        for d in drops {
            self.drop_v(b, st, *d);
        }
        jump_done(b, rs[0], other.then_some(rs[1]));
        b.switch_to_block(done);
        // A remainder is smaller than its divisor, and an integer that
        // fits in a word is always a small one.
        if rem && Self::small(b, st, y) {
            st.ints.insert(r);
        }
        (r, other_param)
    }

    /// `x / y` or `x % y` of small integers, `y` not zero, and with
    /// `other` the other result as a small integer's word, or 0 (`Quot`); a
    /// quotient that leaves the small integers goes to `overflow`, if given
    /// (else it is known not to).
    fn divide_small(b: &mut FunctionBuilder, rem: bool, x: Value, y: Value, overflow: Option<ir::Block>, other: bool) -> (Value, Option<Value>) {
        // Small integers have 63 bits, so neither division overflows i64.
        let n = b.ins().sshr_imm_s(x, 1);
        let d = b.ins().sshr_imm_s(y, 1);
        let q = b.ins().sdiv(n, d);
        // One division: the remainder from the quotient.
        let qd = b.ins().imul(q, d);
        let m = b.ins().isub(n, qd);
        // A negative remainder: one more `|d|` makes it Euclidean, and the
        // quotient moves one step away from `d`'s sign.
        let neg = b.ins().icmp_imm_s(IntCC::SignedLessThan, m, 0);
        let m = if rem || other {
            let ad = b.ins().iabs(d);
            let m1 = b.ins().iadd(m, ad);
            b.ins().select(neg, m1, m)
        } else {
            m
        };
        let q = if !rem || other {
            let dpos = b.ins().icmp_imm_s(IntCC::SignedGreaterThan, d, 0);
            let one = b.ins().iconst(I64, 1);
            let minus = b.ins().iconst(I64, -1);
            let step = b.ins().select(dpos, minus, one);
            let zero = b.ins().iconst(I64, 0);
            let step = b.ins().select(neg, step, zero);
            b.ins().iadd(q, step)
        } else {
            q
        };
        // |m| < |d|: it fits.
        let m_word = |b: &mut FunctionBuilder| {
            let m2 = b.ins().iadd(m, m);
            b.ins().iadd_imm_s(m2, 1)
        };
        if rem {
            let v = m_word(b);
            // Only -2^62 / -1 leaves the small integers.
            let o = other.then(|| {
                let (q2, ov) = b.ins().sadd_overflow(q, q);
                let q1 = b.ins().iadd_imm_s(q2, 1);
                let zero = b.ins().iconst(I64, 0);
                b.ins().select(ov, zero, q1)
            });
            (v, o)
        } else {
            let q2 = match overflow {
                Some(slow) => {
                    let (q2, ov) = b.ins().sadd_overflow(q, q);
                    let ok = b.create_block();
                    b.ins().brif(ov, slow, &[], ok, &[]);
                    b.switch_to_block(ok);
                    q2
                }
                None => b.ins().iadd(q, q),
            };
            let v = b.ins().iadd_imm_s(q2, 1);
            (v, other.then(|| m_word(b)))
        }
    }

    /// `==`, `!=`, `<`, `<=`, `>` or `>=`: a `Bool`, remembered with its
    /// condition (`bool_cond`).
    #[allow(clippy::too_many_arguments)]
    fn compare(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, x: Value, y: Value, owner: Value, drops: &[Value]) -> Value {
        let cc = match p {
            Op::Eq => IntCC::Equal,
            Op::Ne => IntCC::NotEqual,
            Op::Lt => IntCC::SignedLessThan,
            Op::Le => IntCC::SignedLessThanOrEqual,
            Op::Gt => IntCC::SignedGreaterThan,
            _ => IntCC::SignedGreaterThanOrEqual,
        };
        let eq = matches!(p, Op::Eq | Op::Ne);
        let (sx, sy) = (Self::small(b, st, x), Self::small(b, st, y));
        // Small integers compare as their words do. So does a small integer
        // with any other value of its type: the runtime keeps every integer
        // that fits in a word as a small one, so a number object is never
        // equal to it.
        if sx && sy || eq && (sx || sy) {
            let c = b.ins().icmp(cc, x, y);
            for d in drops {
                self.drop_v(b, st, *d);
            }
            // Where `x == 3` holds, `x` is a small integer too.
            let other: Vec<Value> = [x, y].into_iter().filter(|v| !Self::small(b, st, *v)).collect();
            let small_if = if p == Op::Eq { [other, Vec::new()] } else { [Vec::new(), other] };
            return self.bool_cond(b, st, c, if eq { small_if } else { [Vec::new(), Vec::new()] }, (p, x, y));
        }
        let fast = b.create_block();
        let slow = b.create_block();
        b.set_cold_block(slow);
        let done = b.create_block();
        let r = b.append_block_param(done, I8);
        Self::if_small(b, st, &[x, y], fast, slow);
        b.switch_to_block(fast);
        let c = b.ins().icmp(cc, x, y);
        b.ins().jump(done, &[BlockArg::Value(c)]);
        // `Wide::Eq` gives 1 for equal, `Wide::Cmp` the order's sign.
        b.switch_to_block(slow);
        let c2 = if eq {
            let e = self.call_wide(b, st, Wide::Eq, &[x, y, owner])[0];
            b.ins().icmp_imm_s(if p == Op::Eq { IntCC::NotEqual } else { IntCC::Equal }, e, 0)
        } else {
            let s = self.call_wide(b, st, Wide::Cmp, &[x, y])[0];
            b.ins().icmp_imm_s(cc, s, 0)
        };
        for d in drops {
            self.drop_v(b, st, *d);
        }
        b.ins().jump(done, &[BlockArg::Value(c2)]);
        b.switch_to_block(done);
        self.bool_cond(b, st, r, [Vec::new(), Vec::new()], (p, x, y))
    }

    /// A tuple just built whose last component is a tuple object is
    /// flattened (#673): `(a, (b, c))` is `(a, b, c)`.
    fn flatten_tuple(&mut self, b: &mut FunctionBuilder, st: &mut St, x: Value, last: Value) -> Value {
        let check = b.create_block();
        let slow = b.create_block();
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
        let ptr = Self::is_ptr(b, last);
        b.ins().brif(ptr, check, &[], done, &[BlockArg::Value(x)]);
        b.switch_to_block(check);
        b.seal_block(check);
        let info = b.ins().load(I64, flags(), last, 8);
        let kind = b.ins().band_imm_u(info, 0xff);
        let is_tuple = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_TUPLE as i64);
        b.ins().brif(is_tuple, slow, &[], done, &[BlockArg::Value(x)]);
        b.switch_to_block(slow);
        b.seal_block(slow);
        let f = self.call1(b, st, "ck_tuple_flat", &[x]);
        b.ins().jump(done, &[BlockArg::Value(f)]);
        b.switch_to_block(done);
        b.seal_block(done);
        r
    }

    fn borrow(&mut self, b: &mut FunctionBuilder, st: &mut St, op: BOp, a: &[Value]) -> Value {
        match op {
            BOp::Field(i) | BOp::Proj(i) => {
                let x = b.ins().load(I64, flags(), a[0], (w::HDR + 8 * i) as i32);
                self.dup(b, st, x);
                x
            }
            BOp::ProjRest(i) => {
                let k = b.ins().iconst(I64, i as i64);
                self.call1(b, st, "ck_tuple_rest", &[a[0], k])
            }
            BOp::SetField => {
                self.dup(b, st, a[2]);
                // Field `k` is at `HDR + 8k`; the word for `k` is `2k + 1`.
                let off = b.ins().ishl_imm_s(a[1], 2);
                let at = b.ins().iadd(a[0], off);
                b.ins().store(flags(), a[2], at, w::HDR as i32 - 4);
                b.ins().iconst(I64, w::UNIT as i64)
            }
            BOp::Builtin(sym) => self.call_array(b, st, sym, a),
            BOp::ConcatPush => self.call1(b, st, "ck_concat_push", &[a[0], a[1]]),
            BOp::ConcatAll => self.call1(b, st, "ck_concat_all", &[a[0], a[1]]),
            BOp::Prim(p, nat) => self.prim(b, st, p, nat, a, &[], None),
        }
    }

    /// A primitive on `a`; `drops`, among `a`, are dropped after it.
    #[allow(clippy::too_many_arguments)]
    fn prim(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, nat: bool, a: &[Value], drops: &[Value], key: Option<Pair>) -> Value {
        let range = Self::op_range(b, st, p, nat, a);
        let fits = range.is_some_and(|r| SMALL.holds(r)) && a.iter().all(|x| Self::small(b, st, *x));
        let v = self.prim_on(b, st, p, nat, a, drops, fits, key);
        if let Some(r) = range.filter(|r| *r != Range::ANY) {
            st.bounds.insert(v, r);
        }
        v
    }

    /// `prim`, `fits` if the operands and the result are known to be small
    /// integers; `key`, a division's operands as written.
    #[allow(clippy::too_many_arguments)]
    fn prim_on(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, nat: bool, a: &[Value], drops: &[Value], fits: bool, key: Option<Pair>) -> Value {
        let o = self.owner(b, st);
        match p {
            // Words `2x + 1` and `2y + 1`: `2x + 1 + 2y` is `2(x + y) + 1`,
            // and it overflows i64 exactly when `x + y` has more than 63 bits.
            Op::Add => self.arith(
                b,
                st,
                &[a[0], a[1]],
                fits,
                |b, checked| {
                    let y1 = b.ins().iadd_imm_s(a[1], -1);
                    if checked {
                        let (v, o) = b.ins().sadd_overflow(a[0], y1);
                        (v, Some(o))
                    } else {
                        (b.ins().iadd(a[0], y1), None)
                    }
                },
                false,
                Wide::Add,
                drops,
            ),
            // Bounds showing `x >= y`: the obligation holds, and `x - y` fits.
            Op::Sub if nat && fits && Self::range(b, st, a[0]).lo.zip(Self::range(b, st, a[1]).hi).is_some_and(|(x, y)| x >= y) => {
                let y1 = b.ins().iadd_imm_s(a[1], -1);
                b.ins().isub(a[0], y1)
            }
            Op::Sub if nat => {
                let check = b.create_block();
                let fast = b.create_block();
                let slow = b.create_block();
                b.set_cold_block(slow);
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                Self::if_small(b, st, &[a[0], a[1]], check, slow);
                b.switch_to_block(check);
                // `x >= y` is checked only where it isn't proved (§13.3).
                if self.g.proved {
                    b.ins().jump(fast, &[]);
                } else {
                    // Words compare as their integers do.
                    let not_below = b.ins().icmp(IntCC::SignedGreaterThanOrEqual, a[0], a[1]);
                    b.ins().brif(not_below, fast, &[], slow, &[]);
                }
                b.switch_to_block(fast);
                // Both `Nat`s, the first no less: `x - y` fits.
                let y1 = b.ins().iadd_imm_s(a[1], -1);
                let v = b.ins().isub(a[0], y1);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(slow);
                let s = if self.g.proved { self.call_wide(b, st, Wide::Sub, &[a[0], a[1]])[0] } else { self.call_wide(b, st, Wide::NatSub, &[a[0], a[1], o])[0] };
                for d in drops {
                    self.drop_v(b, st, *d);
                }
                b.ins().jump(done, &[BlockArg::Value(s)]);
                b.switch_to_block(done);
                r
            }
            // `2x + 1 - 2y` is `2(x - y) + 1`.
            Op::Sub => self.arith(
                b,
                st,
                &[a[0], a[1]],
                fits,
                |b, checked| {
                    let y1 = b.ins().iadd_imm_s(a[1], -1);
                    if checked {
                        let (v, o) = b.ins().ssub_overflow(a[0], y1);
                        (v, Some(o))
                    } else {
                        (b.ins().isub(a[0], y1), None)
                    }
                },
                false,
                Wide::Sub,
                drops,
            ),
            // `x · 2y` is `2xy`, which overflows i64 exactly when `xy` has
            // more than 63 bits; it is even, so `+ 1` then can't.
            Op::Mul => self.arith(
                b,
                st,
                &[a[0], a[1]],
                fits,
                |b, checked| {
                    let x = b.ins().sshr_imm_s(a[0], 1);
                    let y1 = b.ins().iadd_imm_s(a[1], -1);
                    if checked {
                        let (v, o) = b.ins().smul_overflow(x, y1);
                        (v, Some(o))
                    } else {
                        (b.ins().imul(x, y1), None)
                    }
                },
                true,
                Wide::Mul,
                drops,
            ),
            Op::Div | Op::Rem => self.divide(b, st, p == Op::Rem, a[0], a[1], o, drops, fits, key),
            // `2 - (2x + 1)` is `2(-x) + 1`; it overflows only for `x = -2^62`.
            Op::Neg => self.arith(
                b,
                st,
                &[a[0]],
                fits,
                |b, checked| {
                    let two = b.ins().iconst(I64, 2);
                    if checked {
                        let (v, o) = b.ins().ssub_overflow(two, a[0]);
                        (v, Some(o))
                    } else {
                        (b.ins().isub(two, a[0]), None)
                    }
                },
                false,
                Wide::Neg,
                drops,
            ),
            Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge => self.compare(b, st, p, a[0], a[1], o, drops),
            _ => {
                let r = self.other_prim(b, st, p, nat, a, o);
                for d in drops {
                    self.drop_v(b, st, *d);
                }
                r
            }
        }
    }

    /// The primitives that aren't on integers.
    fn other_prim(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, nat: bool, a: &[Value], o: Value) -> Value {
        match p {
            Op::Concat => self.call1(b, st, "ck_concat", &[a[0], a[1]]),
            Op::TypeApply => self.call1(b, st, "ck_type_apply", &[a[0], a[1]]),
            Op::Len => {
                // Inline for strings, bytes and arrays, which keep their
                // length in their first word (#624); lists go to the runtime.
                let kinds = b.create_block();
                let fast = b.create_block();
                let slow = b.create_block();
                b.set_cold_block(slow);
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                if let Some(facts) = st.arrays.get(&a[0]).copied() {
                    // Read before the loop.
                    b.ins().brif(facts.len, fast, &[], slow, &[]);
                    b.switch_to_block(kinds);
                    b.ins().jump(slow, &[]);
                    b.switch_to_block(fast);
                    b.ins().jump(done, &[BlockArg::Value(facts.len)]);
                } else {
                    let is_ptr = Self::is_ptr(b, a[0]);
                    b.ins().brif(is_ptr, kinds, &[], slow, &[]);
                    b.switch_to_block(kinds);
                    let info = b.ins().load(I64, flags(), a[0], 8);
                    let kind = b.ins().band_imm_s(info, 0xff);
                    let y = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_BYTES as i64);
                    let z = b.ins().icmp_imm_s(IntCC::Equal, kind, checkers_rt::array::K_ARRAY as i64);
                    let any = b.ins().bor(y, z);
                    b.ins().brif(any, fast, &[], slow, &[]);
                    b.switch_to_block(fast);
                    let n = b.ins().load(I64, flags(), a[0], w::HDR as i32);
                    let sh = b.ins().ishl_imm_s(n, 1);
                    let v = b.ins().bor_imm_s(sh, 1);
                    b.ins().jump(done, &[BlockArg::Value(v)]);
                }
                b.switch_to_block(slow);
                let c = self.call1(b, st, "ck_len", &[a[0]]);
                b.ins().jump(done, &[BlockArg::Value(c)]);
                b.switch_to_block(done);
                // A length is a small integer.
                st.ints.insert(r);
                r
            }
            Op::Index => {
                // Inline: a small index into bytes, or into an array of
                // words (#624), in bounds. Packed arrays and everything
                // else go to the runtime. An `Array U8` (`nat` here) is
                // always bytes: no need to check.
                let slow = b.create_block();
                b.set_cold_block(slow);
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                let kinds = b.create_block();
                let bytes = b.create_block();
                let words = b.create_block();
                Self::if_small(b, st, &[a[1]], kinds, slow);
                b.switch_to_block(kinds);
                let i = b.ins().sshr_imm_s(a[1], 1);
                let facts = st.arrays.get(&a[0]).copied();
                let (bytes_at, words_at) = if nat {
                    b.ins().jump(bytes, &[]);
                    (facts.map(|f| f.data), None)
                } else if let Some(f) = facts {
                    let some = b.create_block();
                    b.ins().brif(f.data, some, &[], slow, &[]);
                    b.switch_to_block(some);
                    let is_words = b.ins().icmp_imm_s(IntCC::SignedLessThan, f.data, 0);
                    b.ins().brif(is_words, words, &[], bytes, &[]);
                    (Some(f.data), Some(f.data))
                } else {
                    let info = b.ins().load(I64, flags(), a[0], 8);
                    let kind = b.ins().band_imm_s(info, 0xff);
                    let is_bytes = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_BYTES as i64);
                    let other = b.create_block();
                    b.ins().brif(is_bytes, bytes, &[], other, &[]);
                    b.switch_to_block(other);
                    let is_words = Self::is_word_array(b, info);
                    b.ins().brif(is_words, words, &[], slow, &[]);
                    (None, None)
                };
                for (blk, at, width) in [(bytes, bytes_at, 0), (words, words_at, 3)] {
                    b.switch_to_block(blk);
                    let fast = b.create_block();
                    if self.g.proved {
                        // The index is in bounds: proved (§13.3).
                        b.ins().jump(fast, &[]);
                    } else if let Some(f) = facts {
                        // Words `2i + 1` and `2n + 1` compare as `i` and `n` do.
                        let inb = b.ins().icmp(IntCC::UnsignedLessThan, a[1], f.len);
                        b.ins().brif(inb, fast, &[], slow, &[]);
                    } else {
                        let len = b.ins().load(I64, flags(), a[0], w::HDR as i32);
                        let inb = b.ins().icmp(IntCC::UnsignedLessThan, i, len);
                        b.ins().brif(inb, fast, &[], slow, &[]);
                    }
                    b.switch_to_block(fast);
                    let data = match at {
                        Some(d) => d,
                        None => self.elements(b, a[0]),
                    };
                    let v = if width == 0 {
                        let base = b.ins().iadd(data, i);
                        let byte = b.ins().uload8(I64, flags(), base, 0);
                        let sh = b.ins().ishl_imm_s(byte, 1);
                        b.ins().bor_imm_s(sh, 1)
                    } else {
                        // Without `WORDS_BIT`, if the address is `ArrayFacts`'.
                        let data = if facts.is_some() { b.ins().band_imm_s(data, !WORDS_BIT) } else { data };
                        let off = b.ins().ishl_imm_s(i, width);
                        let base = b.ins().iadd(data, off);
                        let x = b.ins().load(I64, flags(), base, 0);
                        self.dup(b, st, x);
                        x
                    };
                    b.ins().jump(done, &[BlockArg::Value(v)]);
                }
                b.switch_to_block(slow);
                let s = self.call1(b, st, "ck_index", &[a[0], a[1], o]);
                b.ins().jump(done, &[BlockArg::Value(s)]);
                b.switch_to_block(done);
                r
            }
            Op::When => {
                // The cowns' distinctness is checked only where it isn't proved (§13.3).
                let check = b.ins().iconst(I64, i64::from(!self.g.proved));
                self.call1(b, st, "ck_when", &[a[1], a[2], o, check])
            }
            Op::Par => a[0],
            _ => unreachable!("an integer primitive"),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn case(&mut self, b: &mut FunctionBuilder, st: &mut St, scrut: V, arms: &[Arm], lits: &[(E, E)], default: Option<&E>, mode: Mode) {
        let x = self.var(b, st, scrut);
        // Each arm is emitted after the one before, but doesn't follow it.
        let before = st.quots.clone();
        if let Some(cond) = st.conds.get(&x).cloned() {
            if lits.is_empty() && self.on_cond(b, st, &cond, arms, default, &mode) {
                return;
            }
        }
        let fallback = b.create_block();
        if !arms.is_empty() {
            let all_nullary = arms.iter().all(|a| a.fields.is_empty());
            let mut targets = Vec::new();
            if all_nullary {
                // Compare the words: constructors without fields are words.
                // A comparison's `Bool` is one of two: when both have arms,
                // the last needs no test.
                let words: Vec<i64> = arms.iter().map(|a| w::nullary(a.con) as i64).collect();
                let both = st.imm.contains(&x) && words.contains(&self.true_w) && words.contains(&self.false_w);
                for (k, a) in arms.iter().enumerate() {
                    if both && k + 1 == arms.len() {
                        targets.push(b.current_block().expect("a block"));
                        break;
                    }
                    let yes = b.create_block();
                    let no = b.create_block();
                    let c = b.ins().icmp_imm_s(IntCC::Equal, x, w::nullary(a.con) as i64);
                    b.ins().brif(c, yes, &[], no, &[]);
                    targets.push(yes);
                    b.switch_to_block(no);
                }
                if !both {
                    b.ins().jump(fallback, &[]);
                }
            } else {
                // The constructor: in the word, or in the object's header.
                let imm = b.create_block();
                let obj = b.create_block();
                let dispatch = b.create_block();
                let id = b.append_block_param(dispatch, I64);
                let low = b.ins().band_imm_s(x, 7);
                let is_imm = b.ins().icmp_imm_s(IntCC::Equal, low, 2);
                b.ins().brif(is_imm, imm, &[], obj, &[]);
                b.switch_to_block(imm);
                let i1 = b.ins().ushr_imm_s(x, 3);
                b.ins().jump(dispatch, &[BlockArg::Value(i1)]);
                b.switch_to_block(obj);
                let i2 = b.ins().uload32(flags(), x, 12);
                b.ins().jump(dispatch, &[BlockArg::Value(i2)]);
                b.switch_to_block(dispatch);
                for a in arms {
                    let yes = b.create_block();
                    let no = b.create_block();
                    let c = b.ins().icmp_imm_s(IntCC::Equal, id, a.con as i64);
                    b.ins().brif(c, yes, &[], no, &[]);
                    targets.push(yes);
                    b.switch_to_block(no);
                }
                b.ins().jump(fallback, &[]);
            }
            for (a, blk) in arms.iter().zip(targets) {
                b.switch_to_block(blk);
                st.quots.clone_from(&before);
                for (k, f) in a.fields.iter().enumerate() {
                    if let Some(v) = f {
                        let fv = b.ins().load(I64, flags(), x, (w::HDR + 8 * k) as i32);
                        st.vars[*v as usize] = Some(fv);
                    }
                }
                self.emit(b, st, &a.body, mode.again());
            }
        } else if !lits.is_empty() {
            let mut targets = Vec::new();
            for (l, _) in lits {
                let yes = b.create_block();
                let no = b.create_block();
                let c = match l {
                    E::Int(n) => b.ins().icmp_imm_s(IntCC::Equal, x, w::mk_int(*n) as i64),
                    other => {
                        let lv = self.val(b, st, other);
                        let o = self.owner(b, st);
                        let e = self.call1(b, st, "ck_eq", &[x, lv, o]);
                        b.ins().icmp_imm_s(IntCC::Equal, e, self.true_w)
                    }
                };
                b.ins().brif(c, yes, &[], no, &[]);
                targets.push(yes);
                b.switch_to_block(no);
            }
            b.ins().jump(fallback, &[]);
            for ((l, body), blk) in lits.iter().zip(targets) {
                b.switch_to_block(blk);
                st.quots.clone_from(&before);
                // `x` is this integer.
                let added = if matches!(l, E::Int(_)) { Self::assume_small(st, &[x]) } else { Vec::new() };
                self.emit(b, st, body, mode.again());
                Self::forget(st, added);
            }
        } else {
            b.ins().jump(fallback, &[]);
        }
        b.switch_to_block(fallback);
        st.quots.clone_from(&before);
        match default {
            Some(d) => self.emit(b, st, d, mode),
            None => {
                let o = self.owner(b, st);
                let v = self.call1(b, st, "ck_nomatch", &[x, o]);
                self.finish(b, st, &mode, v);
            }
        }
        st.quots = before;
    }

    /// A `match` on a comparison's `Bool`, as a branch on the comparison
    /// itself; false if the arms aren't `True` and `False`.
    fn on_cond(&mut self, b: &mut FunctionBuilder, st: &mut St, cond: &Cond, arms: &[Arm], default: Option<&E>, mode: &Mode) -> bool {
        let side = |a: &Arm| -> Option<usize> {
            let w = w::nullary(a.con) as i64;
            if !a.fields.is_empty() {
                None
            } else if w == self.true_w {
                Some(0)
            } else if w == self.false_w {
                Some(1)
            } else {
                None
            }
        };
        if arms.is_empty() || arms.iter().any(|a| side(a).is_none()) {
            return false;
        }
        // Each side's arm, or the default (or no match).
        let mut bodies: [Option<&E>; 2] = [None, None];
        for a in arms {
            let k = side(a).expect("checked");
            if bodies[k].is_none() {
                bodies[k] = Some(&a.body);
            }
        }
        let blocks = [b.create_block(), b.create_block()];
        b.ins().brif(cond.c, blocks[0], &[], blocks[1], &[]);
        let before = st.quots.clone();
        for k in 0..2 {
            b.switch_to_block(blocks[k]);
            st.quots.clone_from(&before);
            let added = Self::assume_cond(b, st, cond, k);
            match bodies[k].or(default) {
                Some(e) => self.emit(b, st, e, mode.again()),
                None => {
                    let o = self.owner(b, st);
                    let x = self.bool_of(b, cond.c);
                    let v = self.call1(b, st, "ck_nomatch", &[x, o]);
                    self.finish(b, st, mode, v);
                }
            }
            Self::forget_cond(st, added);
        }
        st.quots = before;
        true
    }

    // ── calls from Rust ─────────────────────────────────────────────────────

    /// `ck_invoke(code, env, args, n)`: call `code(env, args…)` (`tail`).
    fn define_invoke(&mut self, fctx: &mut FunctionBuilderContext, ctx: &mut cranelift_codegen::Context) {
        let call_conv = self.m.isa().default_call_conv();
        let mut s = Signature::new(call_conv);
        for _ in 0..4 {
            s.params.push(AbiParam::new(I64));
        }
        s.returns.push(AbiParam::new(I64));
        ctx.func.signature = s;
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, fctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            let (code, env, args, n) = (ps[0], ps[1], ps[2], ps[3]);
            let bad = b.create_block();
            let mut blocks = Vec::new();
            for _ in 0..=self.max_arity {
                blocks.push(b.create_block());
            }
            let calls: Vec<_> = blocks.iter().map(|blk| b.func.dfg.block_call(*blk, &[])).collect();
            let def = b.func.dfg.block_call(bad, &[]);
            let jt = b.create_jump_table(ir::JumpTableData::new(def, &calls));
            let n32 = b.ins().ireduce(I32, n);
            b.ins().br_table(n32, jt);
            for (k, blk) in blocks.iter().enumerate() {
                b.switch_to_block(*blk);
                let mut vs = vec![env];
                for j in 0..k {
                    vs.push(b.ins().load(I64, flags(), args, (8 * j) as i32));
                }
                let sig = b.import_signature(tail_sig(k));
                let inst = b.ins().call_indirect(sig, code, &vs);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            }
            b.switch_to_block(bad);
            b.ins().trap(ir::TrapCode::user(1).unwrap());
            b.seal_all_blocks();
            b.finalize(self.m.isa().frontend_config());
        }
        self.m.define_function(self.invoke, ctx).expect("define invoke");
        self.m.clear_context(ctx);
    }

    /// The program's global closure for `main`.
    pub fn main_closure(&mut self) -> DataId {
        match self.p.defs.get(&self.p.main) {
            Some(DefShape::Fn { func, .. }) => self.closure(*func),
            _ => panic!("`main` is not a function"),
        }
    }

    /// `main(argc, argv)` for an executable: calls `ck_aot_main`.
    pub fn define_c_main(&mut self, desc: &str) {
        let call_conv = self.m.isa().default_call_conv();
        let mut s = Signature::new(call_conv);
        s.params.push(AbiParam::new(I32));
        s.params.push(AbiParam::new(I64));
        s.returns.push(AbiParam::new(I32));
        let main_id = self.m.declare_function("main", Linkage::Export, &s).expect("declare main");
        let mut aot = Signature::new(call_conv);
        aot.params.push(AbiParam::new(I32));
        for _ in 0..7 {
            aot.params.push(AbiParam::new(I64));
        }
        aot.returns.push(AbiParam::new(I32));
        let aot_id = self.m.declare_function("ck_aot_main", Linkage::Import, &aot).expect("declare ck_aot_main");
        let clo = self.main_closure();
        let desc_id = self.raw(desc.as_bytes());
        let mut ctx = self.m.make_context();
        let mut fctx = FunctionBuilderContext::new();
        ctx.func.signature = s;
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fctx);
            let mut st = St::new(Vec::new(), self.p.main, HashSet::new());
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            let d = self.addr(&mut b, &mut st, desc_id);
            let dl = b.ins().iconst(I64, desc.len() as i64);
            let inv = self.fref(&mut b, &mut st, self.invoke);
            let inv = b.ins().func_addr(I64, inv);
            let debug = match self.debug_table() {
                Some(Placed::Word(x)) => b.ins().iconst(I64, x as i64),
                Some(Placed::Data(d, o)) => {
                    let p = self.addr(&mut b, &mut st, d);
                    b.ins().iadd_imm_s(p, o as i64)
                }
                None => b.ins().iconst(I64, 0),
            };
            let mc = self.addr(&mut b, &mut st, clo);
            let ow = b.ins().iconst(I64, self.p.main as i64);
            let r = self.fref(&mut b, &mut st, aot_id);
            let inst = b.ins().call(r, &[ps[0], ps[1], d, dl, inv, debug, mc, ow]);
            let code = b.inst_results(inst)[0];
            b.ins().return_(&[code]);
            b.seal_all_blocks();
            b.finalize(self.m.isa().frontend_config());
        }
        self.m.define_function(main_id, &mut ctx).expect("define main");
    }
}

impl Mode<'_> {
    fn again(&self) -> Self {
        *self
    }
}

/// The integers a word holds inline: 63 bits.
const SMALL: Range = Range { lo: Some(-(1 << 62)), hi: Some((1 << 62) - 1) };
