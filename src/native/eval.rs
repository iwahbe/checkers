//! Compile-time evaluation as native code (D80, §14): `check` declarations
//! (D40) and the values staging computes (§8.9).
//!
//! One in-memory module per program: each closed term becomes a function
//! of no arguments added to it, together with the definitions it needs
//! that aren't compiled yet. It runs on a thread of its own; a runtime
//! error comes back as a message instead of ending the process.

use super::codegen::Gen;
use super::lower::{Lowerer, Program};
use crate::core::{ConId, Globals, Lit, Tm};
use checkers_rt::word::{self as w, W};
use cranelift_jit::JITModule;
use std::rc::Rc;

pub struct Evaluator<'g> {
    g: &'g Globals,
    gen: Gen<'g, JITModule>,
}

impl<'g> Evaluator<'g> {
    pub fn new(g: &'g Globals) -> Evaluator<'g> {
        let module = super::jit_module();
        let mut gen = Gen::new(module, Program::new(g, None), g);
        gen.define_new();
        gen.m.finalize_definitions().expect("finish native code");
        let invoke = gen.m.get_finalized_function(gen.invoke);
        let invoke: checkers_rt::prog::Invoke = unsafe { std::mem::transmute(invoke) };
        checkers_rt::prog::install(&super::descriptor(g, &gen.p), invoke);
        Evaluator { g, gen }
    }

    /// The value of a closed term: an owned word, or the runtime error.
    pub fn eval(&mut self, t: &Tm) -> Result<W, String> {
        let f = Lowerer::new(self.g, None, &mut self.gen.p).add_closed(t);
        super::rc_new(self.g, &mut self.gen.p);
        self.gen.define_new();
        self.gen.m.finalize_definitions().map_err(|e| format!("compiling: {e}"))?;
        let code = self.gen.m.get_finalized_function(self.gen.func_id(f)) as u64;
        let invoke = checkers_rt::prog::prog().invoke;
        checkers_rt::prog::eval_trapped(move || invoke(code, w::ERASED, std::ptr::null(), 0))
    }

    pub fn is_false(&self, v: W) -> bool {
        self.g.well_known.false_con.is_some_and(|c| v == w::nullary(c.0))
    }

    /// As `format` would print it.
    pub fn show(&self, v: W) -> String {
        checkers_rt::ops::show(v, 0)
    }

    pub fn release(&self, v: W) {
        w::drop_w(v)
    }

    /// A value as a term, where it has one (staging, §8.9).
    pub fn reify(&self, v: W) -> Option<Tm> {
        let g = self.g;
        if checkers_rt::obj::is_num(v) {
            let n = checkers_rt::obj::num_of(v);
            return Some(Tm::Lit(Lit::Num(n.to_string().parse().ok()?)));
        }
        if v == w::ERASED || v == w::UNIT {
            return Some(Tm::Tuple(vec![]));
        }
        if let Some(c) = w::con_of(v) {
            let np = g.arity_ty(g.cons[c as usize].ty);
            let mut args: Vec<Tm> = (0..np).map(|_| Tm::Univ(0)).collect();
            if !w::is_nullary(v) {
                for i in 0..w::nfields(v) {
                    args.push(self.reify(w::field(v, i))?);
                }
            }
            return Some(Tm::ConApp(ConId(c), args));
        }
        if !w::is_ptr(v) {
            return None;
        }
        match w::kind(v) {
            w::K_STR => Some(Tm::Lit(Lit::Str(Rc::from(w::str_of(v))))),
            w::K_BYTES => Some(Tm::Lit(Lit::Bytes(Rc::from(w::blob(v))))),
            w::K_TUPLE => (0..w::nfields(v)).map(|i| self.reify(w::slot(v, i))).collect::<Option<Vec<_>>>().map(Tm::Tuple),
            _ => None,
        }
    }
}
