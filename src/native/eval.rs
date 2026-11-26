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
use crate::known::{Builder, Node};
use checkers_rt::word::{self as w, W};
use cranelift_jit::JITModule;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

pub struct Evaluator<'g> {
    g: &'g Globals,
    gen: Gen<'g, JITModule>,
    /// This program's descriptor and `Debug` instances: its own, as other
    /// programs are evaluated at the same time on other threads. Each call
    /// into the runtime is made `within` it.
    prog: &'static checkers_rt::prog::Prog,
}

impl<'g> Evaluator<'g> {
    pub fn new(g: &'g Globals) -> Evaluator<'g> {
        let mut ev = Self::plain(g);
        // The hand-written `Debug` instances (#126), for values shown here.
        if let Some(ir) = super::lower::show_table(g) {
            if let Ok(fs) = ev.eval_ir(&ir) {
                ev.within(|| checkers_rt::prog::set_debug(fs));
            }
        }
        ev
    }

    /// An evaluator for values that are only read back, never shown: no
    /// `Debug` instances compiled (values known at compile time, §8.9).
    pub fn plain(g: &'g Globals) -> Evaluator<'g> {
        let module = super::jit_module();
        let mut gen = Gen::new(module, Program::new(g, None), g);
        gen.probe = true;
        gen.define_new();
        gen.m.finalize_definitions().expect("finish native code");
        let invoke = gen.m.get_finalized_function(gen.invoke);
        let invoke: checkers_rt::prog::Invoke = unsafe { std::mem::transmute(invoke) };
        let prog = checkers_rt::prog::make(&super::descriptor(g, &gen.p), invoke);
        Evaluator { g, gen, prog }
    }

    /// `f`, calling into the runtime for this program.
    fn within<R>(&self, f: impl FnOnce() -> R) -> R {
        checkers_rt::prog::within(self.prog, f)
    }

    /// The value of a closed term: an owned word, or the runtime error.
    pub fn eval(&mut self, t: &Tm) -> Result<W, String> {
        self.eval_limited(t, u64::MAX)
    }

    /// `eval`, stopping with a runtime error after `work` function entries
    /// and loop iterations (`checkers_rt::prog::eval_limited`).
    pub fn eval_limited(&mut self, t: &Tm, work: u64) -> Result<W, String> {
        let spec = super::spec::SpecCx { table: &self.gen.p.specs, staged: None, depth: 0 };
        let ir = super::ir::Compiler { g: self.g, owner: None, spec: Some(spec) }.compile(t);
        self.run(&ir, work)
    }

    /// The value of closed code: an owned word, or the runtime error.
    pub fn eval_ir(&mut self, ir: &super::ir::Ir) -> Result<W, String> {
        self.run(ir, u64::MAX)
    }

    fn run(&mut self, ir: &super::ir::Ir, work: u64) -> Result<W, String> {
        let f = Lowerer::new(self.g, None, &mut self.gen.p).add_closed_ir(ir);
        super::rc_new(self.g, &mut self.gen.p);
        self.gen.define_new();
        self.gen.m.finalize_definitions().map_err(|e| format!("compiling: {e}"))?;
        let code = self.gen.m.get_finalized_function(self.gen.func_id(f)) as u64;
        let invoke = self.prog.invoke;
        self.within(|| checkers_rt::prog::eval_limited(work, move || invoke(code, w::ERASED, std::ptr::null(), 0)))
    }

    pub fn is_false(&self, v: W) -> bool {
        self.g.well_known.false_con.is_some_and(|c| v == w::nullary(c.0))
    }

    /// In the derived form `debug` has (#126), whatever a type's own
    /// `Debug` says: what a failed `check` shows.
    pub fn show(&self, v: W) -> String {
        self.within(|| checkers_rt::ops::show_derived(v, 0))
    }

    /// `v` shown as a value of type `ty` where the type tells more than the
    /// value does: a `Char` as `c'a'`, not its code. Elsewhere as `show`.
    pub fn show_as(&self, v: W, ty: Option<&Tm>) -> String {
        match ty {
            Some(ty) => self.within(|| self.show_typed(v, ty, 0)),
            None => self.show(v),
        }
    }

    /// What is left to write is a list on the heap, not the stack: a long
    /// value takes no more stack than a short one (§13.3).
    fn show_typed(&self, v: W, ty: &Tm, p: u8) -> String {
        let mut out = String::new();
        let mut todo = vec![Shown::Val(v, p, Rc::new(ty.clone()))];
        while let Some(next) = todo.pop() {
            match next {
                Shown::Text(t) => out.push_str(t),
                Shown::Derived(v) => out.push_str(&checkers_rt::ops::show_derived(v, 1)),
                Shown::List(l, elem, first) => {
                    if w::con_of(l) == self.g.well_known.cons.map(|c| c.0) && !w::is_nullary(l) {
                        if !first {
                            out.push_str(", ");
                        }
                        todo.push(Shown::List(w::field(l, 1), elem.clone(), false));
                        todo.push(Shown::Val(w::field(l, 0), 0, elem));
                    }
                }
                Shown::Val(v, p, ty) => self.show_step(v, &ty, p, &mut out, &mut todo),
            }
        }
        out
    }

    /// Write `v`, a value of type `ty`, onto `out`, leaving its parts in `todo`.
    fn show_step(&self, v: W, ty: &Tm, p: u8, out: &mut String, todo: &mut Vec<Shown>) {
        let g = self.g;
        // What this function doesn't handle itself: by the type's descriptor.
        let rt = |out: &mut String| out.push_str(&self.show_by_descriptor(v, ty, p));
        match ty {
            Tm::Def(d) => {
                let info = &g.defs[d.0 as usize];
                if info.module.as_ref() == "std.prelude" && info.name.as_ref() == "Char" && checkers_rt::obj::is_num(v) {
                    let n = checkers_rt::obj::num_of(v);
                    match n.to_string().parse::<u32>().ok().and_then(char::from_u32) {
                        Some(c) => out.push_str(&char_literal(c)),
                        None => rt(out),
                    }
                    return;
                }
                // An alias: the type it names.
                match unfolded(g, ty) {
                    Some(t) => todo.push(Shown::Val(v, p, Rc::new(t))),
                    None => rt(out),
                }
            }
            Tm::TupleTy(ts) if w::is_ptr(v) && w::kind(v) == w::K_TUPLE && w::nfields(v) == ts.len() => {
                out.push('(');
                todo.push(Shown::Text(")"));
                for (i, t) in ts.iter().enumerate().rev() {
                    todo.push(Shown::Val(w::slot(v, i), 0, Rc::new(t.clone())));
                    if i > 0 {
                        todo.push(Shown::Text(", "));
                    }
                }
            }
            // A string as a string literal, as a `Char` is written `c'a'`:
            // a failed `check` may be in a module that doesn't load
            // `std.string`, whose `Debug String` writes it the same way.
            Tm::TyConApp(id, _) if Some(*id) == g.well_known.string && w::is_ptr(v) && w::kind(v) == w::K_BYTES => {
                out.push_str(&string_literal(w::str_of(v)))
            }
            Tm::TyConApp(id, args) => {
                // Stored as its one kept field (#170): the value is that field.
                if let Some((c, k)) = unboxed_con(g, *id) {
                    let ci = &g.cons[c.0 as usize];
                    let (_, m, icit, fty) = &ci.fields[k];
                    if *icit != crate::core::Icit::Expl || *m == crate::core::Mult::Zero {
                        out.push_str(&ci.name);
                        return;
                    }
                    if p > 0 {
                        out.push('(');
                        todo.push(Shown::Text(")"));
                    }
                    out.push_str(&ci.name);
                    out.push(' ');
                    match subst_params(g, fty, args, k) {
                        Some(t) => todo.push(Shown::Val(v, 1, Rc::new(t))),
                        None => out.push_str(&checkers_rt::ops::show_derived(v, 1)),
                    }
                    return;
                }
                let Some(c) = w::con_of(v) else { return rt(out) };
                let wk = &g.well_known;
                if Some(*id) == wk.list && (Some(ConId(c)) == wk.nil || Some(ConId(c)) == wk.cons) {
                    let Some(elem) = args.first() else { return rt(out) };
                    out.push('[');
                    todo.push(Shown::Text("]"));
                    todo.push(Shown::List(v, Rc::new(elem.clone()), true));
                    return;
                }
                let ci = &g.cons[c as usize];
                if ci.ty != *id || (!w::is_nullary(v) && w::nfields(v) != ci.fields.len()) {
                    return rt(out);
                }
                // A field's type is in the context of the type's parameters
                // and the earlier fields; only closed ones are used.
                let mut parts = Vec::new();
                for (i, (_, m, icit, fty)) in ci.fields.iter().enumerate() {
                    if *icit != crate::core::Icit::Expl || *m == crate::core::Mult::Zero {
                        continue;
                    }
                    let fv = w::field(v, i);
                    parts.push(Shown::Text(" "));
                    parts.push(match subst_params(g, fty, args, i) {
                        Some(t) => Shown::Val(fv, 1, Rc::new(t)),
                        None => Shown::Derived(fv),
                    });
                }
                if parts.is_empty() {
                    out.push_str(&ci.name);
                    return;
                }
                if p > 0 {
                    out.push('(');
                    todo.push(Shown::Text(")"));
                }
                out.push_str(&ci.name);
                todo.extend(parts.into_iter().rev());
            }
            _ => rt(out),
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
        self.within(|| w::drop_w(v))
    }

    /// A value of type `ty` (a closed type) as a term, where it has one
    /// (staging, §8.9). The type tells what the value alone doesn't: a
    /// type stored as its one kept field (#170) is that field, a string is
    /// its bytes.
    pub fn reify_as(&self, v: W, ty: &Tm) -> Option<Tm> {
        self.reify_typed(v, Some(ty))
    }

    /// A value as a term, where it has one (staging, §8.9).
    pub fn reify(&self, v: W) -> Option<Tm> {
        self.reify_typed(v, None)
    }

    /// A literal, `()`, or a known value (`Tm::Known`): a graph built by a
    /// depth-first walk with a stack of its own, so a value of any depth
    /// takes the same stack, and each object and type it is read at once.
    fn reify_typed(&self, v: W, ty: Option<&Tm>) -> Option<Tm> {
        let mut r = Reifier { ev: self, b: Builder::default(), types: Vec::new(), type_ids: HashMap::new(), field_types: HashMap::new(), done: Default::default() };
        let t = ty.map(|t| r.intern(t.clone()));
        let root = r.run((v, t))?;
        let k = Arc::new(r.b.finish());
        Some(match k.node(root) {
            Node::Unit => Tm::Tuple(vec![]),
            Node::Con(..) | Node::Tuple(_) => Tm::Known(crate::known::Value::new(k, root)),
            _ => Tm::Lit(k.lit(root)?),
        })
    }
}

/// A word, and the type it is read at (an index into `Reifier::types`), if
/// one is known.
type Key = (W, Option<usize>);

/// What a word read at a type is made of: a node at once, or parts to read
/// first and how to make its node from theirs.
enum Step {
    Leaf(Node),
    Parts(Make, Vec<Key>),
}

enum Make {
    /// The same value at another type (an alias, unfolded).
    Same,
    Con(ConId),
    /// A type stored as its field `k` of `n`: its constructor, the others
    /// erased.
    Kept(ConId, usize, usize),
    Tuple,
}

struct Reifier<'a, 'g> {
    ev: &'a Evaluator<'g>,
    b: Builder,
    /// Types met, by index; `type_ids` finds one by its `Debug` form.
    types: Vec<Tm>,
    type_ids: HashMap<String, usize>,
    /// A field's type at a type: by constructor, the type's index, field.
    field_types: HashMap<(ConId, usize, usize), Option<usize>>,
    /// The node of each word read at each type.
    done: crate::known::FxMap<Key, u32>,
}

impl Reifier<'_, '_> {
    fn intern(&mut self, t: Tm) -> usize {
        let key = format!("{t:?}");
        if let Some(&i) = self.type_ids.get(&key) {
            return i;
        }
        self.types.push(t);
        self.type_ids.insert(key, self.types.len() - 1);
        self.types.len() - 1
    }

    /// Field `k` of constructor `c`'s type at type `t`, if it is closed.
    fn field_type(&mut self, c: ConId, t: usize, k: usize) -> Option<usize> {
        if let Some(r) = self.field_types.get(&(c, t, k)) {
            return *r;
        }
        let g = self.ev.g;
        let r = match &self.types[t] {
            Tm::TyConApp(_, args) => subst_params(g, &g.cons[c.0 as usize].fields[k].3, args, k).map(|ft| self.intern(ft)),
            _ => None,
        };
        self.field_types.insert((c, t, k), r);
        r
    }

    /// The graph's node of `root`: a depth-first walk, its stack a vector.
    fn run(&mut self, root: Key) -> Option<u32> {
        struct Frame {
            key: Key,
            make: Make,
            parts: Vec<Key>,
            next: usize,
        }
        let mut stack: Vec<Frame> = Vec::new();
        let visit = |me: &mut Self, key: Key, stack: &mut Vec<Frame>| -> Option<()> {
            if me.done.contains_key(&key) {
                return Some(());
            }
            match me.step(key)? {
                Step::Leaf(n) => {
                    let id = me.b.add(n);
                    me.done.insert(key, id);
                }
                Step::Parts(make, parts) => stack.push(Frame { key, make, parts, next: 0 }),
            }
            Some(())
        };
        visit(self, root, &mut stack)?;
        while let Some(top) = stack.last_mut() {
            if top.next < top.parts.len() {
                let key = top.parts[top.next];
                top.next += 1;
                visit(self, key, &mut stack)?;
                continue;
            }
            let f = stack.pop().expect("a frame");
            let ids: Vec<u32> = f.parts.iter().map(|k| self.done[k]).collect();
            let id = match f.make {
                Make::Same => ids[0],
                Make::Con(c) => self.b.add(Node::Con(c, ids.into())),
                Make::Kept(c, k, n) => {
                    let unit = self.b.add(Node::Unit);
                    let fields: Vec<u32> = (0..n).map(|j| if j == k { ids[0] } else { unit }).collect();
                    self.b.add(Node::Con(c, fields.into()))
                }
                Make::Tuple if ids.is_empty() => self.b.add(Node::Unit),
                Make::Tuple => self.b.add(Node::Tuple(ids.into())),
            };
            self.done.insert(f.key, id);
        }
        self.done.get(&root).copied()
    }

    /// What `v` read at type `t` is made of; `None` if it has no term.
    fn step(&mut self, (v, t): Key) -> Option<Step> {
        let g = self.ev.g;
        if let Some(t) = t {
            match self.types[t].clone() {
                Tm::Def(_) => {
                    return Some(match unfolded(g, &self.types[t]) {
                        Some(u) => Step::Parts(Make::Same, vec![(v, Some(self.intern(u)))]),
                        None => Step::Parts(Make::Same, vec![(v, None)]),
                    });
                }
                Tm::TupleTy(ts) if w::is_ptr(v) && w::kind(v) == w::K_TUPLE && w::nfields(v) == ts.len() => {
                    let parts = ts.into_iter().enumerate().map(|(i, ft)| (w::slot(v, i), Some(self.intern(ft)))).collect();
                    return Some(Step::Parts(Make::Tuple, parts));
                }
                // A string is stored as its bytes (#170).
                Tm::TyConApp(id, _) if Some(id) == g.well_known.string && w::is_ptr(v) && w::kind(v) == w::K_BYTES => {
                    return Some(Step::Leaf(Node::Str(Box::from(w::str_of(v)))));
                }
                Tm::TyConApp(id, _) => {
                    if let Some((c, k)) = unboxed_con(g, id) {
                        if g.is_dict_type_field(c, k) {
                            return None;
                        }
                        let n = g.cons[c.0 as usize].fields.len();
                        let ft = self.field_type(c, t, k);
                        return Some(Step::Parts(Make::Kept(c, k, n), vec![(v, ft)]));
                    }
                    if let Some(c) = w::con_of(v) {
                        let ci = &g.cons[c as usize];
                        if ci.ty == id && (w::is_nullary(v) || w::nfields(v) == ci.fields.len()) {
                            let c = ConId(c);
                            if w::is_nullary(v) {
                                return Some(Step::Leaf(Node::Con(c, Box::new([]))));
                            }
                            let parts = (0..w::nfields(v)).map(|i| (w::field(v, i), self.field_type(c, t, i))).collect();
                            return Some(Step::Parts(Make::Con(c), parts));
                        }
                    }
                }
                _ => {}
            }
            // What the type doesn't tell: by the value.
            return Some(Step::Parts(Make::Same, vec![(v, None)]));
        }
        if checkers_rt::obj::is_num(v) {
            let n = checkers_rt::obj::num_of(v);
            let lit = Lit::int(n.to_string().parse().ok()?);
            return Some(Step::Leaf(match lit {
                Lit::Num(n) => Node::Int(n),
                Lit::Big(n) => Node::Big((*n).clone()),
                _ => unreachable!("a number"),
            }));
        }
        if v == w::ERASED || v == w::UNIT {
            return Some(Step::Leaf(Node::Unit));
        }
        if let Some(c) = w::con_of(v) {
            let c = ConId(c);
            if w::is_nullary(v) {
                return Some(Step::Leaf(Node::Con(c, Box::new([]))));
            }
            return Some(Step::Parts(Make::Con(c), (0..w::nfields(v)).map(|i| (w::field(v, i), None)).collect()));
        }
        if !w::is_ptr(v) {
            return None;
        }
        match w::kind(v) {
            w::K_BYTES => Some(Step::Leaf(Node::Bytes(Box::from(w::blob(v))))),
            w::K_TUPLE => Some(Step::Parts(Make::Tuple, (0..w::nfields(v)).map(|i| (w::slot(v, i), None)).collect())),
            _ => None,
        }
    }
}

/// What showing a value (`Evaluator::show_typed`) has left to write.
enum Shown {
    /// A value of the type, in argument position if the number is not 0.
    Val(W, u8, Rc<Tm>),
    /// A value shown by the runtime, in argument position.
    Derived(W),
    Text(&'static str),
    /// A list's elements from this cell on; `first`: none written yet.
    List(W, Rc<Tm>, bool),
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

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Barrier};

    /// A thread that makes the evaluator for program `src`, reaches `made`,
    /// then at `go` evaluates the program's own `check`s: the ones false.
    fn checks_of(src: &'static str, made: Arc<Barrier>, go: Arc<Barrier>) -> std::thread::JoinHandle<Vec<String>> {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || {
                let (c, e) = crate::elaborate("prog.ck", src, std::path::Path::new(""));
                assert_eq!(c.errors(), 0, "{}", c.report());
                let (e, user) = e.unwrap();
                let mut ev = super::Evaluator::new(&e.g);
                made.wait();
                go.wait();
                let mut out = Vec::new();
                for (_, span, t) in e.checks.iter().filter(|(m, _, _)| *m == user) {
                    let v = ev.eval(t).unwrap();
                    if ev.is_false(v) {
                        out.push(format!("{user}: the check at {}..{} is false", span.start, span.end));
                    }
                    ev.release(v);
                }
                out
            })
            .unwrap()
    }

    /// Two programs checked at the same time in one process (the unit
    /// tests, a language server): the second's evaluator is made while the
    /// first's is in use, and each still shows values with its own
    /// constructors and `Debug` instances.
    #[test]
    fn each_program_evaluates_with_its_own_descriptor() {
        const A: &str = "module a\n\nimport std.string (debug)\n\nrecord Apple\n    n~Int\n\ncheck debug (Apple 1) == \"Apple 1\"\n\ncheck debug \"ab\" == \"\\\"ab\\\"\"\n";
        const B: &str = "module b\n\nimport std.string (debug)\n\nrecord Berry\n    n~Int\n\nrecord Cherry\n    n~Int\n\ncheck debug (Berry 1) == \"Berry 1\" and debug (Cherry 2) == \"Cherry 2\"\n\ncheck debug \"ab\" == \"\\\"ab\\\"\"\n";
        let (a_made, b_made, go) = (Arc::new(Barrier::new(2)), Arc::new(Barrier::new(2)), Arc::new(Barrier::new(2)));
        // `a` makes its evaluator, then `b` its own, then both evaluate.
        let a = checks_of(A, a_made.clone(), go.clone());
        a_made.wait();
        let b = checks_of(B, b_made.clone(), go);
        b_made.wait();
        let (a, b) = (a.join().unwrap(), b.join().unwrap());
        assert!(a.is_empty() && b.is_empty(), "{a:?} {b:?}");
    }
}
