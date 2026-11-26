//! First-order code → Cranelift (D72, D73, D75).
//!
//! Every function takes its environment (closure) and its arguments as
//! words, in Cranelift's `tail` convention, so calls in tail position are
//! `return_call` (D75). Small integers, `dup`/`drop`, byte indexing and
//! known closure calls are inline; the rest calls the runtime
//! (`checkers_rt`). Global closures, literals and constants' slots are
//! static data.

use super::lower::*;
use crate::core::Globals;
use crate::core::Prim;
use crate::native::ir::Op;
use crate::range::Range;
use checkers_rt::word as w;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::{I32, I64, I8};
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
    ("ck_len", 1, true),
    ("ck_index", 3, true),
    ("ck_big_lit", 2, true),
    ("ck_fail", 3, true),
    ("ck_error", 3, true),
    ("ck_nomatch", 2, true),
    ("ck_caf", 2, true),
    ("ck_apply", 3, true),
    ("ck_when", 2, true),
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
    /// Static values laid out so far, for naming the next.
    statics: usize,
    /// Raw bytes (messages, digits).
    raw: HashMap<Vec<u8>, DataId>,
    pub invoke: FuncId,
    true_w: i64,
    false_w: i64,
    max_arity: usize,
    /// With `Some`: each function's name and machine code as text, as it
    /// is defined, with every runtime error's owner written as 0 (for tests
    /// comparing the code of two functions, which name different owners).
    pub disasm: Option<Vec<(String, String)>>,
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
}

/// A comparison's condition (`I8`), and what holds when it is true or false.
#[derive(Clone)]
struct Cond {
    c: Value,
    /// Small integers when it is true (`x == 3`: `x`), and when false (`x != 3`).
    small_if: [Vec<Value>; 2],
}

enum Mode {
    /// Return the value: one word, or this many (`unbox`).
    Tail(usize),
    /// Jump to this block with the value.
    Val(ir::Block),
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
    pub fn new(mut m: M, p: Program, g: &'p Globals) -> Self {
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
        let invoke = m.declare_function("ck_invoke", Linkage::Export, &is).expect("declare invoke");
        let wk = &g.well_known;
        let nul = |c: Option<crate::core::ConId>| c.map_or(0, |c| w::nullary(c.0) as i64);
        Gen {
            m,
            p,
            g,
            defined: 0,
            invoke_defined: false,
            funcs,
            rt,
            closures: HashMap::new(),
            slots: HashMap::new(),
            lits: HashMap::new(),
            statics: 0,
            raw: HashMap::new(),
            invoke,
            true_w: nul(wk.true_con),
            false_w: nul(wk.false_con),
            max_arity,
            disasm: None,
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

    /// Static data for a value known when the program is compiled: every
    /// object it is made of, in one block that points into itself.
    fn statik(&mut self, v: &Static) -> DataId {
        let id = self.m.declare_data(&format!("ckd_{}", self.statics), Linkage::Local, true, false).expect("declare static data");
        self.statics += 1;
        let mut dd = DataDescription::new();
        let me = self.m.declare_data_in_data(id, &mut dd);
        let mut bytes = Vec::new();
        let mut relocs = Vec::new();
        let _root_at_0 = Self::lay_out(v, &mut bytes, &mut relocs);
        dd.define(bytes.into_boxed_slice());
        dd.set_align(8);
        for (at, to) in relocs {
            dd.write_data_addr(at as u32, me, to as i64);
        }
        self.m.define_data(id, &dd).expect("define static data");
        id
    }

    /// Append `v`'s objects to `out`, its own first; its word, as `Ok` (an
    /// immediate) or `Err` (the offset of its object).
    fn lay_out(v: &Static, out: &mut Vec<u8>, relocs: &mut Vec<(usize, usize)>) -> Result<u64, usize> {
        let (kind, tag, fields) = match v {
            Static::Word(x) => return Ok(*x),
            Static::Str(s) => return Err(Self::lay_out_bytes(w::K_BYTES, s.as_bytes(), out)),
            Static::Bytes(b) => return Err(Self::lay_out_bytes(w::K_BYTES, b, out)),
            Static::Con(c, xs) => (w::K_CON, *c as u64, xs),
            Static::Tuple(xs) => (w::K_TUPLE, 0, xs),
        };
        let at = out.len();
        out.extend_from_slice(&w::STATIC_RC.to_le_bytes());
        out.extend_from_slice(&w::info(kind, fields.len() as u64, tag).to_le_bytes());
        out.resize(at + w::HDR + 8 * fields.len(), 0);
        for (k, f) in fields.iter().enumerate() {
            let slot = at + w::HDR + 8 * k;
            match Self::lay_out(f, out, relocs) {
                Ok(word) => out[slot..slot + 8].copy_from_slice(&word.to_le_bytes()),
                Err(obj) => relocs.push((slot, obj)),
            }
        }
        Err(at)
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
                let code = ctx.compiled_code().and_then(|c| c.vcode.clone()).unwrap_or_default();
                d.push((self.p.funcs[i].name.clone(), code));
            }
            self.m.clear_context(&mut ctx);
        }
        self.defined = self.p.funcs.len();
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
        let params: Vec<Value> = b.block_params(entry).to_vec();
        let vars = vec![None; f.nvars.max(f.params.len() as u32) as usize];
        let mut st = St { vars, imm: HashSet::new(), ints: HashSet::new(), conds: HashMap::new(), bounds: HashMap::new(), owner: f.owner, frefs: HashMap::new(), gvs: HashMap::new(), this: None };
        let env = params[0];
        match &f.kind {
            FnKind::Global | FnKind::Caf => {
                // The body starts at a block of its own, which a call to
                // itself in tail position jumps back to.
                let top = b.create_block();
                let args: Vec<BlockArg> = params.iter().map(|p| BlockArg::Value(*p)).collect();
                let params: Vec<Value> = params.iter().map(|_| b.append_block_param(top, I64)).collect();
                b.ins().jump(top, &args);
                b.switch_to_block(top);
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

    // ── reference counts (D74) ──────────────────────────────────────────────

    /// Is `x` a pointer, a non-zero multiple of 8? Rotated right by 3, its
    /// low bits become its top bits: it is then a number from 1 to 2^61 - 1.
    /// One condition, so a test moved out of a loop holds one register.
    fn is_ptr(b: &mut FunctionBuilder, x: Value) -> Value {
        let r = b.ins().rotr_imm_s(x, 3);
        let m = b.ins().iadd_imm_s(r, -1);
        b.ins().icmp_imm_s(IntCC::UnsignedLessThan, m, (1i64 << 61) - 1)
    }

    fn dup(&mut self, b: &mut FunctionBuilder, st: &mut St, x: Value) {
        if st.imm.contains(&x) || Self::small(b, st, x) {
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
        if st.imm.contains(&x) || Self::small(b, st, x) {
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
    fn finish(b: &mut FunctionBuilder, mode: &Mode, x: Value) {
        let n = match mode {
            Mode::Tail(n) => *n,
            Mode::Val(k) => b.func.dfg.num_block_params(*k),
        };
        let mut xs = vec![x];
        if n > 1 {
            let z = b.ins().iconst(I64, 0);
            xs.resize(n, z);
        }
        Self::finish_all(b, mode, &xs)
    }

    /// Finish with all of `xs`, the words expected.
    fn finish_all(b: &mut FunctionBuilder, mode: &Mode, xs: &[Value]) {
        match mode {
            Mode::Tail(_) => {
                b.ins().return_(xs);
            }
            Mode::Val(k) => {
                let args: Vec<BlockArg> = xs.iter().map(|x| BlockArg::Value(*x)).collect();
                b.ins().jump(*k, &args);
            }
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
            E::Static(v) => {
                let d = self.statik(v);
                self.addr(b, st, d)
            }
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
            E::Var(_) | E::Int(_) | E::Erased | E::Unit | E::Str(_) | E::Bytes(_) | E::Static(_) => {
                let x = self.val(b, st, e);
                Self::finish(b, &mode, x)
            }
            E::BigLit(s) => {
                let (p, n) = self.message(b, st, s);
                let x = self.call1(b, st, "ck_big_lit", &[p, n]);
                Self::finish(b, &mode, x)
            }
            E::Global(d) => {
                let x = self.global(b, st, *d);
                Self::finish(b, &mode, x)
            }
            E::ConFn(c) => {
                let f = self.p.con_wraps[c];
                let d = self.closure(f);
                let x = self.addr(b, st, d);
                Self::finish(b, &mode, x)
            }
            E::Let(x, a, body) => {
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
                    Mode::Val(k) => {
                        let inst = b.ins().call(r, &vs);
                        let xs = b.inst_results(inst).to_vec();
                        Self::finish_all(b, &Mode::Val(k), &xs);
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
                Self::finish(b, &mode, x)
            }
            E::Con { con, fields, reuse } => {
                let vs: Vec<Value> = fields.iter().map(|a| self.val(b, st, a)).collect();
                let tok = reuse.map(|t| self.var(b, st, t));
                let x = self.build_con(b, st, *con, &vs, tok);
                Self::finish(b, &mode, x)
            }
            E::Multi(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                Self::finish_all(b, &mode, &vs)
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
                Self::finish(b, &mode, x)
            }
            E::Borrow { op, args, drops } => {
                let x = self.borrow_e(b, st, *op, args, drops);
                Self::finish(b, &mode, x)
            }
            E::Par(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                let x = self.call_array(b, st, "ck_par", &vs);
                Self::finish(b, &mode, x)
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
                Self::finish(b, &mode, x)
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
                self.prim(b, st, p, nat, &vs, &mine)
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
            Mode::Val(k) => {
                let inst = b.ins().call_indirect(sig, code, &vs);
                let x = b.inst_results(inst)[0];
                b.ins().jump(k, &[BlockArg::Value(x)]);
            }
        }
        b.switch_to_block(slow);
        let p = self.array(b, args);
        let nn = b.ins().iconst(I64, n as i64);
        let x = self.call1(b, st, "ck_apply", &[f, p, nn]);
        Self::finish(b, &mode, x);
    }

    fn bool_of(&self, b: &mut FunctionBuilder, c: Value) -> Value {
        let t = b.ins().iconst(I64, self.true_w);
        let f = b.ins().iconst(I64, self.false_w);
        b.ins().select(c, t, f)
    }

    /// A comparison's `Bool` from its condition, which a `match` on it
    /// branches on instead (`St::conds`).
    fn bool_cond(&self, b: &mut FunctionBuilder, st: &mut St, c: Value, small_if: [Vec<Value>; 2]) -> Value {
        let w = self.bool_of(b, c);
        st.conds.insert(w, Cond { c, small_if });
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
    /// constructors without fields.
    fn immediate(e: &E) -> bool {
        match e {
            E::Let(_, _, x) | E::At(_, x) | E::Dup(_, x) | E::Drop(_, x) | E::DropReuse(_, _, _, x) => Self::immediate(x),
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

    /// An integer operation on `xs`: `fast` (its value, still to be tagged
    /// with `+ 1` if `tag`, and whether it overflowed) if they are small
    /// integers and it doesn't overflow, else the runtime's `slow` on `xs`
    /// and `extra`. The operands' `drops` are dropped on the slow path only:
    /// on the fast path they are small integers. Where the operands' bounds
    /// show that they are small integers and the result one too (`fits`),
    /// only `fast` without its overflow check (`fast(b, false)`).
    #[allow(clippy::too_many_arguments)]
    fn arith(
        &mut self,
        b: &mut FunctionBuilder,
        st: &mut St,
        xs: &[Value],
        fits: bool,
        fast: impl FnOnce(&mut FunctionBuilder, bool) -> (Value, Option<Value>),
        tag: bool,
        slow: &str,
        extra: Option<Value>,
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
        let mut args = xs.to_vec();
        args.extend(extra);
        let s = self.call1(b, st, slow, &args);
        for d in drops {
            self.drop_v(b, st, *d);
        }
        b.ins().jump(done, &[BlockArg::Value(s)]);
        b.switch_to_block(done);
        r
    }

    /// Euclidean `/` or `%` (the remainder never negative), inline when both
    /// are small integers and the divisor isn't zero; otherwise the runtime,
    /// which also reports division by zero. With bounds showing that both
    /// are small integers, the divisor not zero and (for `/`) the result a
    /// small integer (`fits`), there is no runtime path.
    #[allow(clippy::too_many_arguments)]
    fn divide(&mut self, b: &mut FunctionBuilder, st: &mut St, rem: bool, x: Value, y: Value, owner: Value, drops: &[Value], fits: bool) -> Value {
        let ry = Self::range(b, st, y);
        let nonzero = ry.lo.is_some_and(|l| l > 0) || ry.hi.is_some_and(|h| h < 0);
        if Self::small(b, st, x) && Self::small(b, st, y) && nonzero && (rem || fits) {
            return Self::divide_small(b, rem, x, y, None);
        }
        let slow = b.create_block();
        b.set_cold_block(slow);
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
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
        let v = Self::divide_small(b, rem, x, y, (!fits).then_some(slow));
        b.ins().jump(done, &[BlockArg::Value(v)]);
        b.switch_to_block(slow);
        let s = self.call1(b, st, if rem { "ck_rem" } else { "ck_div" }, &[x, y, owner]);
        for d in drops {
            self.drop_v(b, st, *d);
        }
        b.ins().jump(done, &[BlockArg::Value(s)]);
        b.switch_to_block(done);
        // A remainder is smaller than its divisor, and an integer that
        // fits in a word is always a small one.
        if rem && Self::small(b, st, y) {
            st.ints.insert(r);
        }
        r
    }

    /// `x / y` or `x % y` of small integers, `y` not zero; a quotient that
    /// leaves the small integers goes to `overflow`, if given (else it is
    /// known not to).
    fn divide_small(b: &mut FunctionBuilder, rem: bool, x: Value, y: Value, overflow: Option<ir::Block>) -> Value {
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
        if rem {
            let ad = b.ins().iabs(d);
            let m1 = b.ins().iadd(m, ad);
            let m = b.ins().select(neg, m1, m);
            // |m| < |d|: it fits.
            let m2 = b.ins().iadd(m, m);
            b.ins().iadd_imm_s(m2, 1)
        } else {
            let dpos = b.ins().icmp_imm_s(IntCC::SignedGreaterThan, d, 0);
            let one = b.ins().iconst(I64, 1);
            let minus = b.ins().iconst(I64, -1);
            let step = b.ins().select(dpos, minus, one);
            let zero = b.ins().iconst(I64, 0);
            let step = b.ins().select(neg, step, zero);
            let q = b.ins().iadd(q, step);
            let q2 = match overflow {
                // Only -2^62 / -1 leaves the small integers.
                Some(slow) => {
                    let (q2, ov) = b.ins().sadd_overflow(q, q);
                    let ok = b.create_block();
                    b.ins().brif(ov, slow, &[], ok, &[]);
                    b.switch_to_block(ok);
                    q2
                }
                None => b.ins().iadd(q, q),
            };
            b.ins().iadd_imm_s(q2, 1)
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
            return self.bool_cond(b, st, c, if eq { small_if } else { [Vec::new(), Vec::new()] });
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
        b.switch_to_block(slow);
        let c2 = if eq {
            let name = if p == Op::Eq { "ck_eq" } else { "ck_ne" };
            let e = self.call1(b, st, name, &[x, y, owner]);
            b.ins().icmp_imm_s(IntCC::Equal, e, self.true_w)
        } else {
            let s = self.call1(b, st, "ck_cmp", &[x, y]);
            b.ins().icmp_imm_s(cc, s, 0)
        };
        for d in drops {
            self.drop_v(b, st, *d);
        }
        b.ins().jump(done, &[BlockArg::Value(c2)]);
        b.switch_to_block(done);
        self.bool_cond(b, st, r, [Vec::new(), Vec::new()])
    }

    /// A tuple just built whose last component is a tuple object is
    /// flattened (D174): `(a, (b, c))` is `(a, b, c)`.
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
            BOp::Prim(p, nat) => self.prim(b, st, p, nat, a, &[]),
        }
    }

    /// A primitive on `a`; `drops`, among `a`, are dropped after it.
    fn prim(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, nat: bool, a: &[Value], drops: &[Value]) -> Value {
        let range = Self::op_range(b, st, p, nat, a);
        let fits = range.is_some_and(|r| SMALL.holds(r)) && a.iter().all(|x| Self::small(b, st, *x));
        let v = self.prim_on(b, st, p, nat, a, drops, fits);
        if let Some(r) = range.filter(|r| *r != Range::ANY) {
            st.bounds.insert(v, r);
        }
        v
    }

    /// `prim`, `fits` if the operands and the result are known to be small
    /// integers.
    #[allow(clippy::too_many_arguments)]
    fn prim_on(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, nat: bool, a: &[Value], drops: &[Value], fits: bool) -> Value {
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
                "ck_add",
                None,
                drops,
            ),
            // Bounds showing `x >= y`: the obligation holds, and `x - y` fits.
            Op::Sub if nat && fits && Self::range(b, st, a[0]).lo.zip(Self::range(b, st, a[1]).hi).is_some_and(|(x, y)| x >= y) => {
                let y1 = b.ins().iadd_imm_s(a[1], -1);
                b.ins().isub(a[0], y1)
            }
            Op::Sub if nat => {
                // Words compare as their integers do.
                let check = b.create_block();
                let fast = b.create_block();
                let slow = b.create_block();
                b.set_cold_block(slow);
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                Self::if_small(b, st, &[a[0], a[1]], check, slow);
                b.switch_to_block(check);
                let not_below = b.ins().icmp(IntCC::SignedGreaterThanOrEqual, a[0], a[1]);
                b.ins().brif(not_below, fast, &[], slow, &[]);
                b.switch_to_block(fast);
                // Both `Nat`s, the first no less: `x - y` fits.
                let y1 = b.ins().iadd_imm_s(a[1], -1);
                let v = b.ins().isub(a[0], y1);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(slow);
                let s = self.call1(b, st, "ck_natsub", &[a[0], a[1], o]);
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
                "ck_sub",
                None,
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
                "ck_mul",
                None,
                drops,
            ),
            Op::Div | Op::Rem => self.divide(b, st, p == Op::Rem, a[0], a[1], o, drops, fits),
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
                "ck_neg",
                None,
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
                // length in their first word (D133); lists go to the runtime.
                let kinds = b.create_block();
                let fast = b.create_block();
                let slow = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
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
                b.switch_to_block(slow);
                let c = self.call1(b, st, "ck_len", &[a[0]]);
                b.ins().jump(done, &[BlockArg::Value(c)]);
                b.switch_to_block(done);
                // A length is a small integer.
                st.ints.insert(r);
                r
            }
            Op::Index => {
                // Inline: a small index into bytes, in bounds. Other arrays
                // (D133) and everything else go to the runtime. An `Array
                // U8` (`nat` here) is always bytes: no need to check.
                let fast = b.create_block();
                let slow = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                let is_int = b.ins().band_imm_s(a[1], 1);
                let kind_check = b.create_block();
                let check = b.create_block();
                b.ins().brif(is_int, kind_check, &[], slow, &[]);
                b.switch_to_block(kind_check);
                if nat {
                    b.ins().jump(check, &[]);
                } else {
                    let info = b.ins().load(I64, flags(), a[0], 8);
                    let kind = b.ins().band_imm_s(info, 0xff);
                    let is_bytes = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_BYTES as i64);
                    b.ins().brif(is_bytes, check, &[], slow, &[]);
                }
                b.switch_to_block(check);
                let i = b.ins().sshr_imm_s(a[1], 1);
                let len = b.ins().load(I64, flags(), a[0], w::HDR as i32);
                let inb = b.ins().icmp(IntCC::UnsignedLessThan, i, len);
                b.ins().brif(inb, fast, &[], slow, &[]);
                b.switch_to_block(fast);
                // The bytes follow the header, or a slice points at them (#169).
                let ptr = b.ins().load(I64, flags(), a[0], (w::HDR + 8) as i32);
                let inline = b.ins().iadd_imm_s(a[0], (w::HDR + 16) as i64);
                let sliced = b.ins().icmp_imm_s(IntCC::NotEqual, ptr, 0);
                let data = b.ins().select(sliced, ptr, inline);
                let base = b.ins().iadd(data, i);
                let byte = b.ins().uload8(I64, flags(), base, 0);
                let sh = b.ins().ishl_imm_s(byte, 1);
                let v = b.ins().bor_imm_s(sh, 1);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(slow);
                let s = self.call1(b, st, "ck_index", &[a[0], a[1], o]);
                b.ins().jump(done, &[BlockArg::Value(s)]);
                b.switch_to_block(done);
                r
            }
            Op::When => self.call1(b, st, "ck_when", &[a[1], a[2]]),
            Op::Par => a[0],
            _ => unreachable!("an integer primitive"),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn case(&mut self, b: &mut FunctionBuilder, st: &mut St, scrut: V, arms: &[Arm], lits: &[(E, E)], default: Option<&E>, mode: Mode) {
        let x = self.var(b, st, scrut);
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
                // `x` is this integer.
                let added = if matches!(l, E::Int(_)) { Self::assume_small(st, &[x]) } else { Vec::new() };
                self.emit(b, st, body, mode.again());
                Self::forget(st, added);
            }
        } else {
            b.ins().jump(fallback, &[]);
        }
        b.switch_to_block(fallback);
        match default {
            Some(d) => self.emit(b, st, d, mode),
            None => {
                let o = self.owner(b, st);
                let v = self.call1(b, st, "ck_nomatch", &[x, o]);
                Self::finish(b, &mode, v);
            }
        }
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
        for k in 0..2 {
            b.switch_to_block(blocks[k]);
            let added = Self::assume_small(st, &cond.small_if[k]);
            match bodies[k].or(default) {
                Some(e) => self.emit(b, st, e, mode.again()),
                None => {
                    let o = self.owner(b, st);
                    let x = self.bool_of(b, cond.c);
                    let v = self.call1(b, st, "ck_nomatch", &[x, o]);
                    Self::finish(b, mode, v);
                }
            }
            Self::forget(st, added);
        }
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
            let mut st = St { vars: Vec::new(), imm: HashSet::new(), ints: HashSet::new(), conds: HashMap::new(), bounds: HashMap::new(), owner: self.p.main, frefs: HashMap::new(), gvs: HashMap::new(), this: None };
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            let d = self.addr(&mut b, &mut st, desc_id);
            let dl = b.ins().iconst(I64, desc.len() as i64);
            let inv = self.fref(&mut b, &mut st, self.invoke);
            let inv = b.ins().func_addr(I64, inv);
            let debug = match self.p.debug {
                Some(f) => {
                    let r = self.fref(&mut b, &mut st, self.func_id(f));
                    b.ins().func_addr(I64, r)
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

impl Mode {
    fn again(&self) -> Mode {
        match self {
            Mode::Tail(n) => Mode::Tail(*n),
            Mode::Val(k) => Mode::Val(*k),
        }
    }
}

/// The integers a word holds inline: 63 bits.
const SMALL: Range = Range { lo: Some(-(1 << 62)), hi: Some((1 << 62) - 1) };
