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
        let mut ev = Evaluator { g, gen };
        // The hand-written `Debug` instances (#126), for values shown here.
        if let Some(ir) = super::lower::show_table(g) {
            if let Ok(fs) = ev.eval_ir(&ir) {
                checkers_rt::prog::set_debug(fs);
            }
        }
        ev
    }

    /// The value of a closed term: an owned word, or the runtime error.
    pub fn eval(&mut self, t: &Tm) -> Result<W, String> {
        let spec = super::spec::SpecCx { table: &self.gen.p.specs, staged: None, depth: 0 };
        let ir = super::ir::Compiler { g: self.g, owner: None, spec: Some(spec) }.compile(t);
        self.eval_ir(&ir)
    }

    /// The value of closed code: an owned word, or the runtime error.
    pub fn eval_ir(&mut self, ir: &super::ir::Ir) -> Result<W, String> {
        let f = Lowerer::new(self.g, None, &mut self.gen.p).add_closed_ir(ir);
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

    /// In the derived form `debug` has (#126), whatever a type's own
    /// `Debug` says: what a failed `check` shows.
    pub fn show(&self, v: W) -> String {
        checkers_rt::ops::show_derived(v, 0)
    }

    /// `v` shown as a value of type `ty` where the type tells more than the
    /// value does: a `Char` as `c'a'`, not its code. Elsewhere as `show`.
    pub fn show_as(&self, v: W, ty: Option<&Tm>) -> String {
        match ty {
            Some(ty) => self.show_typed(v, ty, 0),
            None => self.show(v),
        }
    }

    fn show_typed(&self, v: W, ty: &Tm, p: u8) -> String {
        let g = self.g;
        // What this function doesn't handle itself: by the type's descriptor.
        let rt = || self.show_by_descriptor(v, ty, p);
        match ty {
            Tm::Def(d) => {
                let info = &g.defs[d.0 as usize];
                if info.module.as_ref() == "std.prelude" && info.name.as_ref() == "Char" && checkers_rt::obj::is_num(v) {
                    let n = checkers_rt::obj::num_of(v);
                    let c = n.to_string().parse::<u32>().ok().and_then(char::from_u32);
                    return c.map(char_literal).unwrap_or_else(rt);
                }
                // An alias: the type it names.
                match unfolded(g, ty) {
                    Some(t) => self.show_typed(v, &t, p),
                    None => rt(),
                }
            }
            Tm::TupleTy(ts) if w::is_ptr(v) && w::kind(v) == w::K_TUPLE && w::nfields(v) == ts.len() => {
                let items: Vec<String> = ts.iter().enumerate().map(|(i, t)| self.show_typed(w::slot(v, i), t, 0)).collect();
                format!("({})", items.join(", "))
            }
            // A string as a string literal, as a `Char` is written `c'a'`:
            // a failed `check` may be in a module that doesn't load
            // `std.string`, whose `Debug String` writes it the same way.
            Tm::TyConApp(id, _) if Some(*id) == g.well_known.string && w::is_ptr(v) && w::kind(v) == w::K_BYTES => {
                string_literal(w::str_of(v))
            }
            Tm::TyConApp(id, args) => {
                // Stored as its one kept field (#170): the value is that field.
                if let Some((c, k)) = unboxed_con(g, *id) {
                    let ci = &g.cons[c.0 as usize];
                    let (_, m, icit, fty) = &ci.fields[k];
                    if *icit != crate::core::Icit::Expl || *m == crate::core::Mult::Zero {
                        return ci.name.to_string();
                    }
                    let shown = match subst_params(g, fty, args, k) {
                        Some(t) => self.show_typed(v, &t, 1),
                        None => checkers_rt::ops::show_derived(v, 1),
                    };
                    return if p > 0 { format!("({} {shown})", ci.name) } else { format!("{} {shown}", ci.name) };
                }
                let Some(c) = w::con_of(v) else { return rt() };
                let wk = &g.well_known;
                if Some(*id) == wk.list && (Some(ConId(c)) == wk.nil || Some(ConId(c)) == wk.cons) {
                    let Some(elem) = args.first() else { return rt() };
                    let mut items = Vec::new();
                    let mut l = v;
                    while w::con_of(l) == wk.cons.map(|c| c.0) && !w::is_nullary(l) {
                        items.push(self.show_typed(w::field(l, 0), elem, 0));
                        l = w::field(l, 1);
                    }
                    return format!("[{}]", items.join(", "));
                }
                let ci = &g.cons[c as usize];
                if ci.ty != *id || (!w::is_nullary(v) && w::nfields(v) != ci.fields.len()) {
                    return rt();
                }
                // A field's type is in the context of the type's parameters
                // and the earlier fields; only closed ones are used.
                let mut shown = Vec::new();
                for (i, (_, m, icit, fty)) in ci.fields.iter().enumerate() {
                    if *icit != crate::core::Icit::Expl || *m == crate::core::Mult::Zero {
                        continue;
                    }
                    let fv = w::field(v, i);
                    let fty = subst_params(g, fty, args, i);
                    shown.push(match fty {
                        Some(t) => self.show_typed(fv, &t, 1),
                        None => checkers_rt::ops::show_derived(fv, 1),
                    });
                }
                if shown.is_empty() {
                    ci.name.to_string()
                } else if p > 0 {
                    format!("({} {})", ci.name, shown.join(" "))
                } else {
                    format!("{} {}", ci.name, shown.join(" "))
                }
            }
            _ => rt(),
        }
    }

    /// `v` shown by the runtime's printer, by the descriptor of the closed
    /// type `ty` (#170).
    fn show_by_descriptor(&self, v: W, ty: &Tm, p: u8) -> String {
        fn rt_ty(d: &crate::core::Desc) -> checkers_rt::desc::Ty {
            match d {
                crate::core::Desc::Known(tag, args) => checkers_rt::desc::Ty::Con { tag: *tag, args: args.iter().map(rt_ty).collect() },
                _ => checkers_rt::desc::Ty::Unknown,
            }
        }
        let tv = crate::core::eval(self.g, &Rc::new(Vec::new()), ty);
        checkers_rt::ops::show_typed_derived(v, &rt_ty(&crate::core::desc_of(self.g, &tv)), p)
    }

    pub fn release(&self, v: W) {
        w::drop_w(v)
    }

    /// A value of type `ty` (a closed type) as a term, where it has one
    /// (staging, §8.9). The type tells what the value alone doesn't: a
    /// type stored as its one kept field (#170) is that field.
    pub fn reify_as(&self, v: W, ty: &Tm) -> Option<Tm> {
        let g = self.g;
        match ty {
            Tm::Def(_) => match unfolded(g, ty) {
                Some(t) => self.reify_as(v, &t),
                None => self.reify(v),
            },
            Tm::TupleTy(ts) if w::is_ptr(v) && w::kind(v) == w::K_TUPLE && w::nfields(v) == ts.len() => {
                (0..ts.len()).map(|i| self.reify_as(w::slot(v, i), &ts[i])).collect::<Option<Vec<_>>>().map(Tm::Tuple)
            }
            // A string is stored as its bytes (#170).
            Tm::TyConApp(id, _) if Some(*id) == g.well_known.string && w::is_ptr(v) && w::kind(v) == w::K_BYTES => {
                Some(Tm::Lit(Lit::Str(Rc::from(w::str_of(v)))))
            }
            Tm::TyConApp(id, args) => {
                let np = g.arity_ty(*id);
                if let Some((c, k)) = unboxed_con(g, *id) {
                    let ci = &g.cons[c.0 as usize];
                    let mut out: Vec<Tm> = (0..np).map(|_| Tm::Univ(0)).collect();
                    for j in 0..ci.fields.len() {
                        out.push(if j != k {
                            Tm::Tuple(vec![])
                        } else if g.is_dict_type_field(c, k) {
                            return None;
                        } else {
                            match subst_params(g, &ci.fields[k].3, args, k) {
                                Some(t) => self.reify_as(v, &t)?,
                                None => self.reify(v)?,
                            }
                        });
                    }
                    return Some(Tm::ConApp(c, out));
                }
                let Some(c) = w::con_of(v) else { return self.reify(v) };
                let ci = &g.cons[c as usize];
                if ci.ty != *id || (!w::is_nullary(v) && w::nfields(v) != ci.fields.len()) {
                    return self.reify(v);
                }
                let mut out: Vec<Tm> = (0..np).map(|_| Tm::Univ(0)).collect();
                if !w::is_nullary(v) {
                    for (i, f) in ci.fields.iter().enumerate() {
                        let fv = w::field(v, i);
                        out.push(match subst_params(g, &f.3, args, i) {
                            Some(t) => self.reify_as(fv, &t)?,
                            None => self.reify(fv)?,
                        });
                    }
                }
                Some(Tm::ConApp(ConId(c), out))
            }
            _ => self.reify(v),
        }
    }

    /// A value as a term, where it has one (staging, §8.9).
    pub fn reify(&self, v: W) -> Option<Tm> {
        let g = self.g;
        if checkers_rt::obj::is_num(v) {
            let n = checkers_rt::obj::num_of(v);
            return Some(Tm::Lit(Lit::int(n.to_string().parse().ok()?)));
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
            w::K_BYTES => Some(Tm::Lit(Lit::Bytes(Rc::from(w::blob(v))))),
            w::K_TUPLE => (0..w::nfields(v)).map(|i| self.reify(w::slot(v, i))).collect::<Option<Vec<_>>>().map(Tm::Tuple),
            _ => None,
        }
    }
}

/// The constructor of type `id` and its one kept field, if the type is
/// stored as that field (#170).
fn unboxed_con(g: &Globals, id: crate::core::TyId) -> Option<(ConId, usize)> {
    let ctors = &g.tys[id.0 as usize].ctors;
    let c = *ctors.first()?;
    g.unboxed_field(c).map(|k| (c, k))
}

/// The type an alias names, as a closed term, if `ty` unfolds.
fn unfolded(g: &Globals, ty: &Tm) -> Option<Tm> {
    let v = crate::core::eval(g, &Rc::new(Vec::new()), ty);
    let u = crate::core::unfold(g, &v)?;
    Some(crate::core::quote(g, 0, &crate::core::force(g, u)))
}

/// A string literal as the lexer reads it, escaped as `std.string`'s
/// `Debug String` escapes it.
fn string_literal(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if (c as u32) < 0x20 || (0x7f..0xa0).contains(&(c as u32)) => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A character literal as the lexer reads it.
fn char_literal(c: char) -> String {
    let body = match c {
        '\'' => "\\'".to_string(),
        '\\' => "\\\\".to_string(),
        '\n' => "\\n".to_string(),
        '\t' => "\\t".to_string(),
        '\r' => "\\r".to_string(),
        c if c.is_control() => format!("\\u{{{:x}}}", c as u32),
        c => c.to_string(),
    };
    format!("c'{body}'")
}

/// A field's type `t` (under the type's parameters, then `earlier` fields)
/// at the parameters `args`, if it mentions no earlier field.
fn subst_params(g: &Globals, t: &Tm, args: &[Tm], earlier: usize) -> Option<Tm> {
    let mut free = std::collections::BTreeSet::new();
    crate::core::free_vars(t, 0, &mut free);
    if free.iter().any(|&k| k < earlier) {
        return None;
    }
    let empty = Rc::new(Vec::new());
    let mut env: Vec<crate::core::Val> = args.iter().map(|a| crate::core::eval(g, &empty, a)).collect();
    let np = env.len();
    env.extend((0..earlier).map(|k| crate::core::Val::var(np + k)));
    let v = crate::core::eval(g, &Rc::new(env), t);
    Some(crate::core::quote(g, np + earlier, &v))
}
