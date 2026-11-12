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
use crate::native::ir::Op;
use checkers_rt::word as w;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::{I32, I64, I8};
use cranelift_codegen::ir::{
    self, AbiParam, AtomicRmwOp, BlockArg, FuncRef, GlobalValue, InstBuilder, MemFlagsData, Signature, StackSlotData,
    StackSlotKind, Value,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use std::collections::HashMap;

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
    ("ck_len", 1, true),
    ("ck_index", 3, true),
    ("ck_format", 1, true),
    ("ck_big_lit", 2, true),
    ("ck_fail", 3, true),
    ("ck_error", 3, true),
    ("ck_nomatch", 2, true),
    ("ck_caf", 2, true),
    ("ck_apply", 3, true),
    ("ck_when", 2, true),
    ("ck_fork", 1, true),
    ("ck_join", 2, true),
    ("ck_par", 2, true),
];

fn flags() -> MemFlagsData {
    MemFlagsData::trusted()
}

/// The most arguments the runtime can call compiled code with
/// (`ck_invoke`).
pub const MAX_INVOKE: usize = 64;

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
    /// Raw bytes (messages, digits).
    raw: HashMap<Vec<u8>, DataId>,
    pub invoke: FuncId,
    true_w: i64,
    false_w: i64,
    max_arity: usize,
}

struct St {
    vars: Vec<Variable>,
    owner: u32,
    frefs: HashMap<FuncId, FuncRef>,
    gvs: HashMap<DataId, GlobalValue>,
}

enum Mode {
    Tail,
    /// Jump to this block with the value.
    Val(ir::Block),
}

fn tail_sig(n: usize) -> Signature {
    let mut s = Signature::new(CallConv::Tail);
    for _ in 0..=n {
        s.params.push(AbiParam::new(I64));
    }
    s.returns.push(AbiParam::new(I64));
    s
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
        let max_arity = MAX_INVOKE;
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
            raw: HashMap::new(),
            invoke,
            true_w: nul(wk.true_con),
            false_w: nul(wk.false_con),
            max_arity,
        }
    }

    // ── static data ─────────────────────────────────────────────────────────

    /// The global closure of function `f` (no free variables).
    fn closure(&mut self, f: u32) -> DataId {
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
            if n > MAX_INVOKE {
                panic!("`{}` takes {n} arguments; native code supports at most {MAX_INVOKE}", self.p.funcs[i].name);
            }
            let id = self.m.declare_function(&format!("ckf_{i}"), Linkage::Local, &tail_sig(n)).expect("declare a function");
            self.funcs.push(id);
        }
        for i in self.defined..self.p.funcs.len() {
            ctx.func.signature = tail_sig(arity_of(&self.p.funcs[i]));
            ctx.func.name = ir::UserFuncName::user(0, i as u32);
            {
                let mut b = FunctionBuilder::new(&mut ctx.func, &mut fctx);
                self.function(&mut b, i);
                b.seal_all_blocks();
                b.finalize(self.m.isa().frontend_config());
            }
            if let Err(e) = self.m.define_function(self.funcs[i], &mut ctx) {
                panic!("native code for `{}`: {e:?}", self.p.funcs[i].name);
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
        let vars: Vec<Variable> = (0..f.nvars.max(f.params.len() as u32)).map(|_| b.declare_var(I64)).collect();
        let mut st = St { vars, owner: f.owner, frefs: HashMap::new(), gvs: HashMap::new() };
        let env = params[0];
        match &f.kind {
            FnKind::Global | FnKind::Caf => {
                for (k, v) in f.params.iter().enumerate() {
                    b.def_var(st.vars[*v as usize], params[k + 1]);
                }
                self.emit(b, &mut st, &f.body, Mode::Tail);
            }
            FnKind::Lambda { captured } => {
                for (k, v) in f.params.iter().enumerate() {
                    b.def_var(st.vars[*v as usize], params[k + 1]);
                }
                for (k, v) in captured.iter().enumerate() {
                    let x = b.ins().load(I64, flags(), env, (w::HDR + 8 + 8 * k) as i32);
                    self.dup(b, &mut st, x);
                    b.def_var(st.vars[*v as usize], x);
                }
                self.drop_v(b, &mut st, env);
                self.emit(b, &mut st, &f.body, Mode::Tail);
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
        b.ins().iconst(I64, st.owner as i64)
    }

    fn message(&mut self, b: &mut FunctionBuilder, st: &mut St, m: &str) -> (Value, Value) {
        let d = self.raw(m.as_bytes());
        let p = self.addr(b, st, d);
        let n = b.ins().iconst(I64, m.len() as i64);
        (p, n)
    }

    // ── reference counts (D74) ──────────────────────────────────────────────

    fn is_ptr(b: &mut FunctionBuilder, x: Value) -> Value {
        let low = b.ins().band_imm_s(x, 7);
        let a = b.ins().icmp_imm_s(IntCC::Equal, low, 0);
        let nz = b.ins().icmp_imm_s(IntCC::NotEqual, x, 0);
        b.ins().band(a, nz)
    }

    fn dup(&mut self, b: &mut FunctionBuilder, _st: &mut St, x: Value) {
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

    fn var(&self, b: &mut FunctionBuilder, st: &St, v: V) -> Value {
        b.use_var(st.vars[v as usize])
    }

    // ── expressions ─────────────────────────────────────────────────────────

    /// Finish with `x`: return it, or pass it on.
    fn finish(b: &mut FunctionBuilder, mode: &Mode, x: Value) {
        match mode {
            Mode::Tail => {
                b.ins().return_(&[x]);
            }
            Mode::Val(k) => {
                b.ins().jump(*k, &[BlockArg::Value(x)]);
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
            E::Str(s) => {
                let d = self.lit(w::K_STR, s.as_bytes());
                self.addr(b, st, d)
            }
            E::Bytes(x) => {
                let d = self.lit(w::K_BYTES, x);
                self.addr(b, st, d)
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

    fn emit(&mut self, b: &mut FunctionBuilder, st: &mut St, e: &E, mode: Mode) {
        match e {
            E::Var(_) | E::Int(_) | E::Erased | E::Unit | E::Str(_) | E::Bytes(_) => {
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
                let v = self.val(b, st, a);
                b.def_var(st.vars[*x as usize], v);
                self.emit(b, st, body, mode)
            }
            E::Call { f, args, .. } => {
                let mut vs = vec![b.ins().iconst(I64, 0)];
                for a in args {
                    vs.push(self.val(b, st, a));
                }
                let r = self.fref(b, st, self.funcs[*f as usize]);
                match mode {
                    Mode::Tail => {
                        b.ins().return_call(r, &vs);
                    }
                    Mode::Val(k) => {
                        let inst = b.ins().call(r, &vs);
                        let x = b.inst_results(inst)[0];
                        b.ins().jump(k, &[BlockArg::Value(x)]);
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
            E::Tuple(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                let x = self.alloc(b, st, w::info(w::K_TUPLE, vs.len() as u64, 0), w::HDR + 8 * vs.len());
                for (k, v) in vs.iter().enumerate() {
                    b.ins().store(flags(), *v, x, (w::HDR + 8 * k) as i32);
                }
                Self::finish(b, &mode, x)
            }
            E::Borrow { op, args, drops } => {
                let vs: Vec<Value> = args.iter().map(|a| self.val(b, st, a)).collect();
                let x = self.borrow(b, st, *op, &vs);
                for d in drops {
                    let dv = self.var(b, st, *d);
                    self.drop_v(b, st, dv);
                }
                Self::finish(b, &mode, x)
            }
            E::Par(xs) => {
                let vs: Vec<Value> = xs.iter().map(|a| self.val(b, st, a)).collect();
                let x = self.call_array(b, st, "ck_par", &vs);
                Self::finish(b, &mode, x)
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
                b.def_var(st.vars[*tok as usize], t);
                self.emit(b, st, body, mode)
            }
            E::Case { scrut, arms, lits, default } => self.case(b, st, *scrut, arms, lits, default.as_deref(), mode),
        }
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
            Mode::Tail => {
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

    /// Both small integers?
    fn both_int(b: &mut FunctionBuilder, x: Value, y: Value) -> Value {
        let a = b.ins().band(x, y);
        b.ins().band_imm_s(a, 1)
    }

    /// `fast` if both are small integers and it doesn't overflow, else the
    /// runtime's `slow`.
    #[allow(clippy::too_many_arguments)]
    fn arith(
        &mut self,
        b: &mut FunctionBuilder,
        st: &mut St,
        x: Value,
        y: Value,
        fast: impl FnOnce(&mut FunctionBuilder) -> (Value, Value),
        slow: &str,
        extra: Option<Value>,
    ) -> Value {
        let try_fast = b.create_block();
        let slow_b = b.create_block();
        let done = b.create_block();
        let r = b.append_block_param(done, I64);
        let ints = Self::both_int(b, x, y);
        b.ins().brif(ints, try_fast, &[], slow_b, &[]);
        b.switch_to_block(try_fast);
        let (v, overflow) = fast(b);
        b.ins().brif(overflow, slow_b, &[], done, &[BlockArg::Value(v)]);
        b.switch_to_block(slow_b);
        let mut args = vec![x, y];
        args.extend(extra);
        let s = self.call1(b, st, slow, &args);
        b.ins().jump(done, &[BlockArg::Value(s)]);
        b.switch_to_block(done);
        r
    }

    fn borrow(&mut self, b: &mut FunctionBuilder, st: &mut St, op: BOp, a: &[Value]) -> Value {
        match op {
            BOp::Field(i) | BOp::Proj(i) => {
                let x = b.ins().load(I64, flags(), a[0], (w::HDR + 8 * i) as i32);
                self.dup(b, st, x);
                x
            }
            BOp::Builtin(sym) => self.call_array(b, st, sym, a),
            BOp::Prim(p, nat) => self.prim(b, st, p, nat, a),
        }
    }

    fn prim(&mut self, b: &mut FunctionBuilder, st: &mut St, p: Op, nat: bool, a: &[Value]) -> Value {
        let o = self.owner(b, st);
        match p {
            Op::Add => self.arith(
                b,
                st,
                a[0],
                a[1],
                |b| {
                    let y1 = b.ins().iadd_imm_s(a[1], -1);
                    b.ins().sadd_overflow(a[0], y1)
                },
                "ck_add",
                None,
            ),
            Op::Sub if nat => {
                // Words compare as their integers do.
                let ints = Self::both_int(b, a[0], a[1]);
                let fast = b.create_block();
                let slow = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                let ok_ints = b.ins().icmp_imm_s(IntCC::NotEqual, ints, 0);
                let not_below = b.ins().icmp(IntCC::SignedGreaterThanOrEqual, a[0], a[1]);
                let go = b.ins().band(ok_ints, not_below);
                b.ins().brif(go, fast, &[], slow, &[]);
                b.switch_to_block(fast);
                let d = b.ins().isub(a[0], a[1]);
                let v = b.ins().iadd_imm_s(d, 1);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(slow);
                let s = self.call1(b, st, "ck_natsub", &[a[0], a[1], o]);
                b.ins().jump(done, &[BlockArg::Value(s)]);
                b.switch_to_block(done);
                r
            }
            Op::Sub => self.arith(
                b,
                st,
                a[0],
                a[1],
                |b| {
                    let (d, ov) = b.ins().ssub_overflow(a[0], a[1]);
                    // (2x+1) - (2y+1) = 2(x-y): add the tag back.
                    let one = b.ins().iconst(I64, 1);
                    let (v, ov2) = b.ins().sadd_overflow(d, one);
                    (v, b.ins().bor(ov, ov2))
                },
                "ck_sub",
                None,
            ),
            Op::Mul => self.arith(
                b,
                st,
                a[0],
                a[1],
                |b| {
                    let x = b.ins().sshr_imm_s(a[0], 1);
                    let y1 = b.ins().iadd_imm_s(a[1], -1);
                    let (m, ov) = b.ins().smul_overflow(x, y1);
                    (b.ins().iadd_imm_s(m, 1), ov)
                },
                "ck_mul",
                None,
            ),
            Op::Div => self.call1(b, st, "ck_div", &[a[0], a[1], o]),
            Op::Rem => self.call1(b, st, "ck_rem", &[a[0], a[1], o]),
            Op::Neg => self.call1(b, st, "ck_neg", &[a[0]]),
            Op::Eq | Op::Ne => {
                let ints = Self::both_int(b, a[0], a[1]);
                let fast = b.create_block();
                let slow = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                b.ins().brif(ints, fast, &[], slow, &[]);
                b.switch_to_block(fast);
                let cc = if p == Op::Eq { IntCC::Equal } else { IntCC::NotEqual };
                let c = b.ins().icmp(cc, a[0], a[1]);
                let v = self.bool_of(b, c);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(slow);
                let name = if p == Op::Eq { "ck_eq" } else { "ck_ne" };
                let s = self.call1(b, st, name, &[a[0], a[1], o]);
                b.ins().jump(done, &[BlockArg::Value(s)]);
                b.switch_to_block(done);
                r
            }
            Op::Lt | Op::Le | Op::Gt | Op::Ge => {
                let cc = match p {
                    Op::Lt => IntCC::SignedLessThan,
                    Op::Le => IntCC::SignedLessThanOrEqual,
                    Op::Gt => IntCC::SignedGreaterThan,
                    _ => IntCC::SignedGreaterThanOrEqual,
                };
                let ints = Self::both_int(b, a[0], a[1]);
                let fast = b.create_block();
                let slow = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I8);
                b.ins().brif(ints, fast, &[], slow, &[]);
                b.switch_to_block(fast);
                let c = b.ins().icmp(cc, a[0], a[1]);
                b.ins().jump(done, &[BlockArg::Value(c)]);
                b.switch_to_block(slow);
                let s = self.call1(b, st, "ck_cmp", &[a[0], a[1]]);
                let c2 = b.ins().icmp_imm_s(cc, s, 0);
                b.ins().jump(done, &[BlockArg::Value(c2)]);
                b.switch_to_block(done);
                self.bool_of(b, r)
            }
            Op::Concat => self.call1(b, st, "ck_concat", &[a[0], a[1]]),
            Op::Len => {
                // Inline for strings, bytes and arrays, which keep their
                // length in their first word (D133); lists go to the runtime.
                let kinds = b.create_block();
                let fast = b.create_block();
                let slow = b.create_block();
                let done = b.create_block();
                let r = b.append_block_param(done, I64);
                let low = b.ins().band_imm_s(a[0], 7);
                let aligned = b.ins().icmp_imm_s(IntCC::Equal, low, 0);
                let nonzero = b.ins().icmp_imm_s(IntCC::NotEqual, a[0], 0);
                let is_ptr = b.ins().band(aligned, nonzero);
                b.ins().brif(is_ptr, kinds, &[], slow, &[]);
                b.switch_to_block(kinds);
                let info = b.ins().load(I64, flags(), a[0], 8);
                let kind = b.ins().band_imm_s(info, 0xff);
                let s = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_STR as i64);
                let y = b.ins().icmp_imm_s(IntCC::Equal, kind, w::K_BYTES as i64);
                let z = b.ins().icmp_imm_s(IntCC::Equal, kind, checkers_rt::array::K_ARRAY as i64);
                let sy = b.ins().bor(s, y);
                let any = b.ins().bor(sy, z);
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
                let base = b.ins().iadd(a[0], i);
                let byte = b.ins().uload8(I64, flags(), base, (w::HDR + 8) as i32);
                let sh = b.ins().ishl_imm_s(byte, 1);
                let v = b.ins().bor_imm_s(sh, 1);
                b.ins().jump(done, &[BlockArg::Value(v)]);
                b.switch_to_block(slow);
                let s = self.call1(b, st, "ck_index", &[a[0], a[1], o]);
                b.ins().jump(done, &[BlockArg::Value(s)]);
                b.switch_to_block(done);
                r
            }
            Op::Format => self.call1(b, st, "ck_format", &[a[0]]),
            Op::When => self.call1(b, st, "ck_when", &[a[1], a[2]]),
            Op::Fork => self.call1(b, st, "ck_fork", &[a[1]]),
            Op::Join => self.call1(b, st, "ck_join", &[a[1], a[2]]),
            Op::Par => a[0],
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn case(&mut self, b: &mut FunctionBuilder, st: &mut St, scrut: V, arms: &[Arm], lits: &[(E, E)], default: Option<&E>, mode: Mode) {
        let x = self.var(b, st, scrut);
        let fallback = b.create_block();
        if !arms.is_empty() {
            let all_nullary = arms.iter().all(|a| a.fields.is_empty());
            let mut targets = Vec::new();
            if all_nullary {
                // Compare the words: constructors without fields are words.
                for a in arms {
                    let yes = b.create_block();
                    let no = b.create_block();
                    let c = b.ins().icmp_imm_s(IntCC::Equal, x, w::nullary(a.con) as i64);
                    b.ins().brif(c, yes, &[], no, &[]);
                    targets.push(yes);
                    b.switch_to_block(no);
                }
                b.ins().jump(fallback, &[]);
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
                        b.def_var(st.vars[*v as usize], fv);
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
            for ((_, body), blk) in lits.iter().zip(targets) {
                b.switch_to_block(blk);
                self.emit(b, st, body, mode.again());
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
        for _ in 0..6 {
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
            let mut st = St { vars: Vec::new(), owner: self.p.main, frefs: HashMap::new(), gvs: HashMap::new() };
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let ps = b.block_params(entry).to_vec();
            let d = self.addr(&mut b, &mut st, desc_id);
            let dl = b.ins().iconst(I64, desc.len() as i64);
            let inv = self.fref(&mut b, &mut st, self.invoke);
            let inv = b.ins().func_addr(I64, inv);
            let mc = self.addr(&mut b, &mut st, clo);
            let ow = b.ins().iconst(I64, self.p.main as i64);
            let r = self.fref(&mut b, &mut st, aot_id);
            let inst = b.ins().call(r, &[ps[0], ps[1], d, dl, inv, mc, ow]);
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
            Mode::Tail => Mode::Tail,
            Mode::Val(k) => Mode::Val(*k),
        }
    }
}
