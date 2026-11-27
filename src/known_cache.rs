//! Known values kept across builds (§8.9), in `.checkers/known/` beside the
//! checked file, as Z3's answers are (#591): those the type checker's own
//! evaluation gives (`force_kept`), those native code computes for the type
//! checker, and those folding computes in native code.
//!
//! A value is stored under a key: a digest of the term computed, its type,
//! the `ckc` executable, and every definition and type the computation can
//! reach, transitively. A definition counts by its type and body (sealed
//! bodies too) and whether it is sealed, a type by its parameters and
//! constructors. So editing a
//! function computes again exactly the values that can run it, and nothing
//! else. In a key and in a stored value, definitions, types and
//! constructors are named by module and name, never by their numbers,
//! which depend on the order modules load: a value is read back into
//! another build's numbering, and isn't reused if a name it holds is gone.
//!
//! A cache reads one program's code (`Program`): the type checker's
//! definitions, or native code's, with staged bodies and specialized
//! copies. A copy has no definition of its own: it is named by the
//! definition it copies and its body, which holds the known arguments put
//! into it.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use crate::core::{eval, unfold_all, force_meta, quote, CaseTm, ConId, DefId, Elim, Env, Globals, Head, Icit, Lit, Mult, Prim, Tm, TyId, Val};
use crate::known::{Builder, Code, Known, Node, Value};
use crate::native::ir::{Ir, Lit as IrLit};
use crate::native::lower::{SNode, Static};
use checkers_rt::word as w;

const HEADER: &str = "checkers known 1";

/// What a key covers besides the term: a definition or a type (with its
/// constructors).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Item {
    Def(u32),
    Ty(u32),
}

/// Definitions and constructors by name, for reading a stored value, and
/// how many definitions and types there were when it was built.
struct ByName {
    defs_len: usize,
    tys_len: usize,
    defs: HashMap<String, u32>,
    tys: HashMap<String, u32>,
    cons: HashMap<String, u32>,
}

/// The code a cache reads: the definitions, and for native code the bodies
/// staging gave them and the copies specialization made.
#[derive(Clone, Copy)]
pub struct Program<'a> {
    pub g: &'a Globals,
    pub staged: Option<&'a crate::stage::Staged>,
    pub specs: Option<&'a crate::native::spec::Specs>,
}

impl<'a> Program<'a> {
    /// The type checker's definitions, as declared.
    pub fn of(g: &'a Globals) -> Program<'a> {
        Program { g, staged: None, specs: None }
    }

    /// The copy `d` is, if it is one.
    fn copy(&self, d: u32) -> Option<&'a crate::native::spec::Copy> {
        self.specs.and_then(|s| s.copy(d))
    }

    /// The staged definition `d` is, if it is one: its index and name.
    fn extra(&self, d: u32) -> Option<(usize, &'a (String, Tm))> {
        let i = (d as usize).checked_sub(self.g.defs.len())?;
        self.staged.and_then(|s| s.extra.get(i)).map(|e| (i, e))
    }

    /// Whether `d` names a definition of this program.
    fn has_def(&self, d: u32) -> bool {
        (d as usize) < self.g.defs.len() || self.extra(d).is_some() || self.copy(d).is_some()
    }
}

/// Static data written already: the graph (kept, so its address isn't
/// reused), its digest, and the items it names.
type Written = (Arc<Static>, String, Vec<Item>);

/// Names and digests, worked out once per program: a cache reads one
/// program's code.
#[derive(Default)]
pub struct KnownCache {
    def_names: HashMap<u32, String>,
    ty_names: HashMap<u32, String>,
    /// Each item's digest and the items it mentions.
    items: HashMap<Item, (String, Vec<Item>)>,
    /// A digest of each item and every item it reaches.
    closures: HashMap<Item, String>,
    /// Static data written already, by graph and node: its digest and the
    /// items it names (the graph kept, so its address isn't reused).
    statics: HashMap<(usize, u32), Written>,
    /// From names back to numbers, for reading a stored value: built when
    /// first needed, again if more have been declared since.
    by_name: Option<ByName>,
    /// Values of the type checker's evaluation read or computed in this
    /// build, by key: the fuel each took, and its term.
    whnfs: HashMap<String, (u64, Tm)>,
}

/// Where known values are kept, if anywhere.
fn dir() -> Option<std::path::PathBuf> {
    crate::verify::cache_dir().map(|d| d.join("known"))
}

/// A name written in one token.
fn escape(s: &str) -> String {
    s.replace('%', "%25").replace(' ', "%20").replace('\n', "%0A")
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    s.len().is_multiple_of(2).then_some(())?;
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(s.get(i..i + 2)?, 16).ok()).collect()
}

/// The term a value read back stands for: as `reify` makes one.
fn term_of(k: Arc<Known>, root: u32) -> Option<Tm> {
    Some(match k.node(root) {
        Node::Unit | Node::Erased => Tm::Tuple(vec![]),
        Node::Con(..) | Node::Tuple(_) | Node::Array(..) | Node::Closure(_) | Node::Pap(_) => Tm::Known(Value::new(k, root)),
        _ => Tm::Lit(k.lit(root)?),
    })
}

impl KnownCache {
    /// A definition's name, as every build of the same text gives it: its
    /// module and name, and how many before it have both.
    /// A staged definition is named by its name and how many before it
    /// have it; a copy, by its digest, of the definition it copies and its
    /// body.
    fn def_name(&mut self, p: &Program, d: u32) -> String {
        if let Some(n) = self.def_names.get(&d) {
            return n.clone();
        }
        let g = p.g;
        let n = if let Some(info) = g.defs.get(d as usize) {
            let k = g.defs[..d as usize].iter().filter(|i| i.module == info.module && i.name == info.name).count();
            escape(&format!("{}.{}#{k}", info.module, info.name))
        } else if let Some((i, (name, _))) = p.extra(d) {
            let k = p.staged.map_or(0, |s| s.extra[..i].iter().filter(|e| e.0 == *name).count());
            escape(&format!("staged {name}#{k}"))
        } else {
            let (digest, _) = self.item(p, Item::Def(d));
            format!("copy%20{digest}")
        };
        self.def_names.insert(d, n.clone());
        n
    }

    fn ty_name(&mut self, g: &Globals, t: u32) -> String {
        if let Some(n) = self.ty_names.get(&t) {
            return n.clone();
        }
        let info = &g.tys[t as usize];
        let k = g.tys[..t as usize].iter().filter(|i| i.module == info.module && i.name == info.name).count();
        let n = escape(&format!("{}.{}#{k}", info.module, info.name));
        self.ty_names.insert(t, n.clone());
        n
    }

    fn con_name(&mut self, g: &Globals, c: u32) -> String {
        let con = &g.cons[c as usize];
        format!("{}.{}", self.ty_name(g, con.ty.0), escape(&con.name))
    }

    /// Value `v` written with names: each node a line, parts first, the
    /// value last. The items it names are added to `items`.
    fn encode(&mut self, p: &Program, k: &Known, root: u32, items: &mut Vec<Item>) -> String {
        let g = p.g;
        let nodes = k.reachable(root);
        let at: HashMap<u32, usize> = nodes.iter().enumerate().map(|(i, n)| (*n, i)).collect();
        let ids = |xs: &[u32]| xs.iter().map(|x| at[x].to_string()).collect::<Vec<_>>().join(" ");
        let mut out = String::new();
        for &n in &nodes {
            let line = match k.node(n) {
                Node::Int(i) => format!("i {i}"),
                Node::Big(b) => format!("b {b}"),
                Node::Str(s) => format!("s {}", hex(s.as_bytes())),
                Node::Bytes(b) => format!("y {}", hex(b)),
                Node::Unit => "u".into(),
                Node::Erased => "e".into(),
                Node::Con(c, xs) => {
                    items.push(Item::Ty(g.cons[c.0 as usize].ty.0));
                    format!("c {} {}", self.con_name(g, c.0), ids(xs))
                }
                Node::Tuple(xs) => format!("t {}", ids(xs)),
                Node::Array(l, xs) => format!("a {l} {}", ids(xs)),
                Node::Closure(Code::Def(d)) => {
                    items.push(Item::Def(d.0));
                    format!("fd {}", self.def_name(p, d.0))
                }
                Node::Closure(Code::Con(c)) => {
                    items.push(Item::Ty(g.cons[c.0 as usize].ty.0));
                    format!("fc {}", self.con_name(g, c.0))
                }
                Node::Pap(xs) => format!("p {}", ids(xs)),
            };
            out += line.trim_end();
            out.push('\n');
        }
        out
    }

    /// Static data `s` at `root` written with names, compactly: the names
    /// it holds, then each node, parts first, the value last. `None` if it
    /// holds what a name can't say (a function of the program's first-order
    /// code, an immediate of no such kind). The types it names are added to
    /// `items`, and the definitions it holds as functions.
    fn encode_static(&mut self, p: &Program, s: &Static, root: u32, items: &mut Vec<Item>) -> Option<Vec<u8>> {
        let g = p.g;
        let nodes = s.reachable(root);
        // Each node's place among those written (nodes are numbered densely).
        let mut at = vec![0u32; root as usize + 1];
        for (i, n) in nodes.iter().enumerate() {
            at[*n as usize] = i as u32;
        }
        // Names by first use, each written once.
        let mut names: Vec<String> = Vec::new();
        let mut name_at: HashMap<(u8, u32), usize> = HashMap::new();
        let mut name = |this: &mut KnownCache, kind: u8, n: u32, items: &mut Vec<Item>| -> Option<usize> {
            if let Some(i) = name_at.get(&(kind, n)) {
                return Some(*i);
            }
            let text = match kind {
                b'c' => {
                    let con = g.cons.get(n as usize)?;
                    items.push(Item::Ty(con.ty.0));
                    this.con_name(g, n)
                }
                _ => {
                    items.push(Item::Def(n));
                    format!("def {}", this.def_name(p, n))
                }
            };
            names.push(text);
            name_at.insert((kind, n), names.len() - 1);
            Some(names.len() - 1)
        };
        let mut body = Vec::new();
        let ids = |out: &mut Vec<u8>, xs: &[u32]| {
            varint(out, xs.len() as u64);
            for x in xs {
                varint(out, at[*x as usize] as u64);
            }
        };
        for &n in &nodes {
            match s.node(n) {
                SNode::Word(x) if w::is_int(*x) => {
                    body.push(0);
                    let i = w::int_of(*x);
                    varint(&mut body, ((i << 1) ^ (i >> 63)) as u64);
                }
                SNode::Word(x) if w::is_nullary(*x) => {
                    let c = name(self, b'c', u32::try_from(*x >> 3).ok()?, items)?;
                    body.push(1);
                    varint(&mut body, c as u64);
                }
                SNode::Word(x) if *x == w::UNIT => body.push(2),
                SNode::Word(x) if *x == w::ERASED => body.push(3),
                SNode::Word(_) => return None,
                SNode::Big(b) => {
                    body.push(4);
                    blob(&mut body, b.to_string().as_bytes());
                }
                SNode::Bytes(b) => {
                    body.push(5);
                    blob(&mut body, b);
                }
                SNode::Obj { kind, tag, fields } if *kind == w::K_CON => {
                    let c = name(self, b'c', u32::try_from(*tag).ok()?, items)?;
                    body.push(6);
                    varint(&mut body, c as u64);
                    ids(&mut body, fields);
                }
                SNode::Obj { kind, fields, .. } if *kind == w::K_TUPLE => {
                    body.push(7);
                    ids(&mut body, fields);
                }
                SNode::Obj { .. } => return None,
                SNode::Array { layout, elems } => {
                    body.push(8);
                    body.push(*layout);
                    ids(&mut body, elems);
                }
                SNode::Global(d) if p.has_def(*d) => {
                    let d = name(self, b'd', *d, items)?;
                    body.push(9);
                    varint(&mut body, d as u64);
                }
                SNode::ConFn(c) => {
                    let c = name(self, b'c', *c, items)?;
                    body.push(10);
                    varint(&mut body, c as u64);
                }
                SNode::Global(_) | SNode::Code(_) => return None,
            }
        }
        let mut out = STATIC_HEADER.to_vec();
        varint(&mut out, names.len() as u64);
        for n in &names {
            blob(&mut out, n.as_bytes());
        }
        varint(&mut out, nodes.len() as u64);
        out.extend_from_slice(&body);
        Some(out)
    }

    /// `t`'s `Debug` form with every number naming a definition, type or
    /// constructor replaced by its name, and each known value by a digest
    /// of its form written with names; the items it names are added to
    /// `items`.
    fn render(&mut self, p: &Program, t: &Tm, items: &mut Vec<Item>) -> String {
        fn strip(c: &mut KnownCache, p: &Program, t: &Tm, items: &mut Vec<Item>) -> Tm {
            match t {
                Tm::Known(v) => {
                    let text = c.encode(p, &v.graph, v.id, items);
                    Tm::Lit(Lit::Str(Rc::from(format!("\0known {}", crate::verify::digest(&text)))))
                }
                _ => t.map_sub(|x, _| strip(c, p, x, items)),
            }
        }
        let s = format!("{:?}", strip(self, p, t, items));
        self.rename(p, &s, items)
    }

    fn rename(&mut self, p: &Program, s: &str, items: &mut Vec<Item>) -> String {
        let g = p.g;
        let mut out = String::with_capacity(s.len());
        let mut rest = s;
        loop {
            // The next `DefId(`, `TyId(` or `ConId(`: one pass over the text.
            let mut from = 0;
            let next = loop {
                let Some(j) = rest[from..].find("Id(") else { break None };
                let j = from + j;
                if let Some(pre) = ["DefId(", "TyId(", "ConId("].into_iter().find(|p| rest[..j + 3].ends_with(p)) {
                    break Some((j + 3 - pre.len(), pre));
                }
                from = j + 3;
            };
            let Some((i, pre)) = next else {
                out += rest;
                return out;
            };
            out += &rest[..i];
            let after = &rest[i + pre.len()..];
            let digits = after.chars().take_while(|c| c.is_ascii_digit()).count();
            let n: Option<u32> = after[..digits].parse().ok();
            match (n, after[digits..].starts_with(')')) {
                (Some(n), true) => {
                    let name = match pre {
                        "DefId(" if p.has_def(n) => {
                            items.push(Item::Def(n));
                            format!("def {}", self.def_name(p, n))
                        }
                        "TyId(" if (n as usize) < g.tys.len() => {
                            items.push(Item::Ty(n));
                            format!("ty {}", self.ty_name(g, n))
                        }
                        "ConId(" if (n as usize) < g.cons.len() => {
                            items.push(Item::Ty(g.cons[n as usize].ty.0));
                            format!("con {}", self.con_name(g, n))
                        }
                        _ => format!("{pre}{n})"),
                    };
                    out += &format!("<{name}>");
                    rest = &after[digits + 1..];
                }
                _ => {
                    out += pre;
                    rest = after;
                }
            }
        }
    }

    /// Closed code `ir` written with names, as a key needs it: `None` if
    /// it has a part a name can't say. The items it names are added to
    /// `items`.
    fn ir_text(&mut self, p: &Program, ir: &Ir, out: &mut String, items: &mut Vec<Item>) -> Option<()> {
        use std::fmt::Write;
        let g = p.g;
        let con = |c: u32, items: &mut Vec<Item>, this: &mut KnownCache| -> Option<String> {
            g.cons.get(c as usize)?;
            items.push(Item::Ty(g.cons[c as usize].ty.0));
            Some(this.con_name(g, c))
        };
        let list = |this: &mut KnownCache, xs: &[std::sync::Arc<Ir>], out: &mut String, items: &mut Vec<Item>| -> Option<()> {
            out.push('(');
            for x in xs {
                this.ir_text(p, x, out, items)?;
                out.push(',');
            }
            out.push(')');
            Some(())
        };
        match ir {
            Ir::Lit(IrLit::Num(n)) => write!(out, "{n}").unwrap(),
            Ir::Lit(IrLit::Big(s)) => write!(out, "big {s}").unwrap(),
            Ir::Lit(IrLit::Str(s)) => write!(out, "{s:?}").unwrap(),
            Ir::Lit(IrLit::Bytes(b)) => write!(out, "b{b:?}").unwrap(),
            Ir::Static(v, id) => {
                let (digest, named) = self.static_digest(p, v, *id)?;
                items.extend(named);
                write!(out, "#{digest}").unwrap();
            }
            Ir::Erased => out.push('_'),
            Ir::Global(d) if p.has_def(d.0) => {
                items.push(Item::Def(d.0));
                write!(out, "<def {}>", self.def_name(p, d.0)).unwrap();
            }
            Ir::Con(c, xs) => {
                write!(out, "<con {}>", con(c.0, items, self)?).unwrap();
                list(self, xs, out, items)?;
            }
            Ir::Tuple(xs) => list(self, xs, out, items)?,
            Ir::At(_, x) => self.ir_text(p, x, out, items)?,
            Ir::Prim(op, xs, nat) => {
                write!(out, "{op:?}{nat}").unwrap();
                list(self, xs, out, items)?;
            }
            Ir::Call(h, xs) => {
                self.ir_text(p, h, out, items)?;
                list(self, xs, out, items)?;
            }
            Ir::ConFn(c) => write!(out, "<fn {}>", con(c.0, items, self)?).unwrap(),
            _ => return None,
        }
        Some(())
    }

    /// An item's digest, and the items its text names.
    fn item(&mut self, p: &Program, it: Item) -> (String, Vec<Item>) {
        if let Some(r) = self.items.get(&it) {
            return r.clone();
        }
        let g = p.g;
        let mut deps = Vec::new();
        let text = match it {
            Item::Def(d) if (d as usize) < g.defs.len() => {
                let info = &g.defs[d as usize];
                let ty = info.ty.clone();
                // Native code runs the body staging gave it, if any.
                let body = p.staged.and_then(|s| s.bodies.get(&crate::core::DefId(d))).cloned().or_else(|| info.body.clone());
                // Whether it is sealed changes once its module is checked:
                // `closure` adds it.
                let (opaque, comptime) = (info.opaque, format!("{:?}", info.comptime));
                let ty = self.render(p, &ty, &mut deps);
                let body = match &body {
                    Some(b) => self.render(p, b, &mut deps),
                    // A builtin: the runtime's code, which the executable covers.
                    None => "builtin".into(),
                };
                format!("def {}\nty {ty}\nbody {body}\nopaque {opaque} comptime {comptime}", self.def_name(p, d))
            }
            Item::Def(d) => {
                if let Some((_, (_, body))) = p.extra(d) {
                    format!("def {}\nbody {}", self.def_name(p, d), self.render(p, body, &mut deps))
                } else if let Some(c) = p.copy(d) {
                    // Its name is this text's digest: the definition it
                    // copies, and its body, which holds the arguments put in.
                    deps.push(Item::Def(c.of.0));
                    let body = self.render(p, &c.body, &mut deps);
                    format!("copy of {}\ndepth {} binders {:?}\nbody {body}", self.def_name(p, c.of.0), c.depth, c.binders)
                } else {
                    format!("unknown {d}")
                }
            }
            Item::Ty(t) => {
                let info = &g.tys[t as usize];
                let params = info.params.clone();
                let ctors = info.ctors.clone();
                let flags = format!("record {} abstract {} positive {:?} negative {:?} dicts {}", info.is_record, info.is_abstract, info.positive, info.negative, info.dicts);
                let mut text = format!("ty {}\n{flags}\n", self.ty_name(g, t));
                for (x, ty) in &params {
                    text += &format!("param {x} {}\n", self.render(p, ty, &mut deps));
                }
                for c in ctors {
                    let con = &g.cons[c.0 as usize];
                    let (tag, fields) = (con.tag, con.fields.clone());
                    text += &format!("con {} {tag}\n", self.con_name(g, c.0));
                    for (x, m, i, f) in &fields {
                        text += &format!("field {x} {m:?} {i:?} {}\n", self.render(p, f, &mut deps));
                    }
                }
                text
            }
        };
        deps.sort();
        deps.dedup();
        let r = (crate::verify::digest(&text), deps);
        // A definition not checked yet gets its body later: not remembered.
        if !unchecked(g, it) {
            self.items.insert(it, r.clone());
        }
        r
    }

    /// A module has sealed its functions (§6): the digests of everything
    /// that reaches them change.
    pub fn sealed(&mut self) {
        self.closures.clear();
    }

    /// A digest of `it` and every item it reaches, each by name and digest,
    /// and whether every definition among them is checked (`unchecked`).
    fn closure(&mut self, p: &Program, it: Item) -> (String, bool) {
        if let Some(c) = self.closures.get(&it) {
            return (c.clone(), true);
        }
        let mut todo = vec![it];
        let mut seen = HashSet::new();
        let mut parts = Vec::new();
        let mut checked = true;
        while let Some(x) = todo.pop() {
            if !seen.insert(x) {
                continue;
            }
            checked &= !unchecked(p.g, x);
            let (d, deps) = self.item(p, x);
            let name = match x {
                Item::Def(d) => {
                    let sealed = p.g.defs.get(d as usize).is_some_and(|i| i.sealed);
                    format!("def {}{}", self.def_name(p, d), if sealed { " sealed" } else { "" })
                }
                Item::Ty(t) => format!("ty {}", self.ty_name(p.g, t)),
            };
            parts.push(format!("{name} {d}"));
            todo.extend(deps);
        }
        parts.sort();
        let c = crate::verify::digest(&parts.join("\n"));
        if checked {
            self.closures.insert(it, c.clone());
        }
        (c, checked)
    }

    /// A key over `text` and everything `items` reach, and whether every
    /// definition they reach is checked.
    fn key_of(&mut self, p: &Program, text: &str, mut items: Vec<Item>) -> (String, bool) {
        items.sort();
        items.dedup();
        let mut checked = true;
        let mut parts: Vec<String> = items
            .into_iter()
            .map(|it| {
                let (c, ok) = self.closure(p, it);
                checked &= ok;
                c
            })
            .collect();
        parts.sort();
        let content = format!("{HEADER}\n{}\n{text}\n{}", crate::verify::tool_identity(), parts.join("\n"));
        (crate::verify::digest(&content), checked)
    }

    /// The key of `t` at type `ty`: what the module comment says.
    pub fn key(&mut self, g: &Globals, t: &Tm, ty: Option<&Tm>) -> String {
        let p = Program::of(g);
        let mut items = Vec::new();
        let term = self.render(&p, t, &mut items);
        let ty = ty.map(|ty| self.render(&p, ty, &mut items)).unwrap_or_default();
        self.key_of(&p, &format!("{term}\n{ty}"), items).0
    }

    /// The key of the weak-head normal form the type checker's evaluation
    /// gives closed term `t` (`force_kept`): `None` if `t` reaches a
    /// definition not checked yet, whose body is still to come.
    fn whnf_key(&mut self, g: &Globals, t: &Tm) -> Option<String> {
        let p = Program::of(g);
        let mut items = Vec::new();
        let term = self.render(&p, t, &mut items);
        let (key, checked) = self.key_of(&p, &format!("whnf {term}"), items);
        checked.then_some(key)
    }

    /// The key of closed code `ir` that folding computes, in program `p`:
    /// `None` if it has a part a name can't say.
    pub fn code_key(&mut self, p: &Program, ir: &Ir) -> Option<String> {
        let mut items = Vec::new();
        let mut text = String::from("folded ");
        self.ir_text(p, ir, &mut text, &mut items)?;
        Some(self.key_of(p, &text, items).0)
    }

    /// Constructors by name, for reading a stored value.
    fn by_name(&mut self, g: &Globals) -> &ByName {
        if self.by_name.as_ref().is_none_or(|b| b.defs_len != g.defs.len() || b.tys_len != g.tys.len()) {
            let p = Program::of(g);
            let defs = (0..g.defs.len() as u32).map(|d| (self.def_name(&p, d), d)).collect();
            let tys = (0..g.tys.len() as u32).map(|t| (self.ty_name(g, t), t)).collect();
            let cons = (0..g.cons.len() as u32).map(|c| (self.con_name(g, c), c)).collect();
            self.by_name = Some(ByName { defs_len: g.defs.len(), tys_len: g.tys.len(), defs, tys, cons });
        }
        self.by_name.as_ref().unwrap()
    }

    /// The lines stored under `key`, after the header.
    fn read(key: &str) -> Option<String> {
        let text = std::fs::read_to_string(dir()?.join(key)).ok()?;
        let rest = text.strip_prefix(HEADER)?.strip_prefix('\n')?;
        Some(rest.to_string())
    }

    /// Keep `text` under `key`.
    fn write(key: &str, text: &str) {
        write_file(key, format!("{HEADER}\n{text}").as_bytes());
    }

    /// The value stored under `key`, read into this build's numbering.
    pub fn recall(&mut self, g: &Globals, key: &str) -> Option<Tm> {
        let text = Self::read(key)?;
        let (k, root) = self.read_known(g, &text)?;
        term_of(k, root)
    }

    /// A value written by `encode`, read into this build's numbering.
    fn read_known(&mut self, g: &Globals, text: &str) -> Option<(Arc<Known>, u32)> {
        let ByName { defs, cons, .. } = self.by_name(g);
        let mut b = Builder::default();
        let mut ids: Vec<u32> = Vec::new();
        for l in text.lines() {
            let (tag, rest) = l.split_once(' ').unwrap_or((l, ""));
            let parts = |r: &str| -> Option<Box<[u32]>> { r.split_whitespace().map(|x| ids.get(x.parse::<usize>().ok()?).copied()).collect() };
            let node = match tag {
                "i" => Node::Int(rest.parse().ok()?),
                "b" => Node::Big(rest.parse().ok()?),
                "s" => Node::Str(String::from_utf8(unhex(rest)?).ok()?.into()),
                "y" => Node::Bytes(unhex(rest)?.into()),
                "u" => Node::Unit,
                "e" => Node::Erased,
                "c" => {
                    let (name, xs) = rest.split_once(' ').unwrap_or((rest, ""));
                    Node::Con(crate::core::ConId(*cons.get(name)?), parts(xs)?)
                }
                "t" => Node::Tuple(parts(rest)?),
                "a" => {
                    let (l, xs) = rest.split_once(' ').unwrap_or((rest, ""));
                    Node::Array(l.parse().ok()?, parts(xs)?)
                }
                "fd" => Node::Closure(Code::Def(crate::core::DefId(*defs.get(rest)?))),
                "fc" => Node::Closure(Code::Con(crate::core::ConId(*cons.get(rest)?))),
                "p" => Node::Pap(parts(rest)?),
                _ => return None,
            };
            ids.push(b.add(node));
        }
        let root = *ids.last()?;
        Some((Arc::new(b.finish()), root))
    }

    /// Keep `value` under `key`, if it is a value that can be kept.
    pub fn store(&mut self, g: &Globals, key: &str, value: &Tm) {
        if dir().is_none() {
            return;
        }
        let (k, root) = match value {
            Tm::Known(v) => (v.graph.clone(), v.id),
            Tm::Lit(l) => Known::of_lit(l),
            Tm::Tuple(xs) if xs.is_empty() => {
                let mut b = Builder::default();
                let r = b.add(Node::Unit);
                (Arc::new(b.finish()), r)
            }
            _ => return,
        };
        let text = self.encode(&Program::of(g), &k, root, &mut Vec::new());
        Self::write(key, &text);
    }

    /// The static data stored under `key` (folding's), read into this
    /// build's numbering: the graph and its root.
    pub fn recall_static(&mut self, g: &Globals, key: &str) -> Option<(Arc<Static>, u32)> {
        let bytes = std::fs::read(dir()?.join(key)).ok()?;
        let (s, root, cons) = self.read_static(g, &bytes)?;
        let s = Arc::new(s);
        // Code that uses the value has its key without writing it again:
        // these bytes are how it is written.
        let items = cons.iter().map(|c| Item::Ty(g.cons[*c as usize].ty.0)).collect();
        self.remember_static(&s, root, &bytes, items);
        Some((s, root))
    }

    /// Static data written by `encode_static`, and the constructors it names.
    fn read_static(&mut self, g: &Globals, bytes: &[u8]) -> Option<(Static, u32, Vec<u32>)> {
        let mut r = Reader { b: bytes.strip_prefix(STATIC_HEADER)?, at: 0 };
        let by_name = &self.by_name(g).cons;
        let cons: Vec<Option<u32>> = (0..r.varint()?).map(|_| Some(std::str::from_utf8(r.blob()?).ok().and_then(|n| by_name.get(n).copied()))).collect::<Option<_>>()?;
        let con = |r: &mut Reader| cons.get(r.varint()? as usize).copied().flatten();
        let mut s = Static::default();
        let n = r.varint()? as usize;
        let mut ids: Vec<u32> = Vec::with_capacity(n.min(bytes.len()));
        for _ in 0..n {
            let parts = |r: &mut Reader, ids: &[u32]| -> Option<Box<[u32]>> { (0..r.varint()?).map(|_| ids.get(r.varint()? as usize).copied()).collect() };
            let node = match r.byte()? {
                0 => {
                    let z = r.varint()?;
                    let i = ((z >> 1) as i64) ^ -((z & 1) as i64);
                    SNode::Word(w::mk_int(Some(i).filter(|i| w::fits(*i as i128))?))
                }
                1 => SNode::Word(w::nullary(con(&mut r)?)),
                2 => SNode::Word(w::UNIT),
                3 => SNode::Word(w::ERASED),
                4 => SNode::Big(std::str::from_utf8(r.blob()?).ok()?.parse().ok()?),
                5 => SNode::Bytes(r.blob()?.into()),
                6 => {
                    let c = con(&mut r)?;
                    SNode::Obj { kind: w::K_CON, tag: c as u64, fields: parts(&mut r, &ids)? }
                }
                7 => SNode::Obj { kind: w::K_TUPLE, tag: 0, fields: parts(&mut r, &ids)? },
                8 => {
                    let layout = r.byte()?;
                    SNode::Array { layout, elems: parts(&mut r, &ids)? }
                }
                // Functions aren't kept: folding's values have none.
                _ => return None,
            };
            ids.push(s.add(node));
        }
        (r.at == r.b.len()).then_some(())?;
        let root = *ids.last()?;
        Some((s, root, cons.into_iter().flatten().collect()))
    }

    /// Static data `s` at `root` written with names (`encode_static`),
    /// remembered by graph and node: its digest and the items it names.
    fn static_digest(&mut self, p: &Program, s: &Arc<Static>, root: u32) -> Option<(String, Vec<Item>)> {
        let at = (Arc::as_ptr(s) as usize, root);
        if let Some((_, d, items)) = self.statics.get(&at) {
            return Some((d.clone(), items.clone()));
        }
        let mut items = Vec::new();
        let bytes = self.encode_static(p, s, root, &mut items)?;
        Some(self.remember_static(s, root, &bytes, items))
    }

    fn remember_static(&mut self, s: &Arc<Static>, root: u32, bytes: &[u8], mut items: Vec<Item>) -> (String, Vec<Item>) {
        items.sort();
        items.dedup();
        let d = crate::verify::digest_bytes(bytes);
        self.statics.insert((Arc::as_ptr(s) as usize, root), (s.clone(), d.clone(), items.clone()));
        (d, items)
    }

    /// Keep static data `s` at `root` under `key`, if it can be kept.
    pub fn store_static(&mut self, p: &Program, key: &str, s: &Arc<Static>, root: u32) {
        if dir().is_none() {
            return;
        }
        let mut items = Vec::new();
        if let Some(bytes) = self.encode_static(p, s, root, &mut items) {
            write_file(key, &bytes);
            // Code that uses the value has its key without writing it again.
            self.remember_static(s, root, &bytes, items);
        }
    }

    /// Term `t` written with names, as tokens each followed by a space
    /// (`read_tm` reads them back): `None` if it holds an unknown, which
    /// names nothing another build has.
    fn write_tm(&mut self, g: &Globals, t: &Tm, out: &mut String) -> Option<()> {
        let p = Program::of(g);
        let tok = |out: &mut String, s: &str| {
            out.push_str(s);
            out.push(' ');
        };
        let mult = |m: Mult| match m {
            Mult::Zero => "0",
            Mult::One => "1",
            Mult::Many => "w",
        };
        let icit = |i: Icit| if i == Icit::Expl { "e" } else { "i" };
        match t {
            Tm::Var(i) => tok(out, &format!("v{i}")),
            Tm::Def(d) => {
                tok(out, "d");
                tok(out, &self.def_name(&p, d.0));
            }
            Tm::TyCon(x) => {
                tok(out, "T");
                tok(out, &self.ty_name(g, x.0));
            }
            Tm::Con(c) => {
                tok(out, "C");
                tok(out, &self.con_name(g, c.0));
            }
            Tm::Meta(_) => return None,
            Tm::Univ(u) => tok(out, &format!("u{u}")),
            Tm::Pi(x, m, i, a, b) => {
                for s in ["P", &escape(x), mult(*m), icit(*i)] {
                    tok(out, s);
                }
                self.write_tm(g, a, out)?;
                self.write_tm(g, b, out)?;
            }
            Tm::Lam(x, m, i, b) => {
                for s in ["L", &escape(x), mult(*m), icit(*i)] {
                    tok(out, s);
                }
                self.write_tm(g, b, out)?;
            }
            Tm::App(f, a, i, m) => {
                for s in ["A", icit(*i), mult(*m)] {
                    tok(out, s);
                }
                self.write_tm(g, f, out)?;
                self.write_tm(g, a, out)?;
            }
            Tm::Let(x, m, ty, v, b) => {
                for s in ["E", &escape(x), mult(*m)] {
                    tok(out, s);
                }
                for t in [ty, v, b] {
                    self.write_tm(g, t, out)?;
                }
            }
            Tm::Lit(l) => tok(out, &lit_token(l)),
            Tm::TupleTy(ts) | Tm::Tuple(ts) => {
                tok(out, &format!("{}{}", if matches!(t, Tm::Tuple(_)) { "U" } else { "Y" }, ts.len()));
                for t in ts {
                    self.write_tm(g, t, out)?;
                }
            }
            Tm::Proj(x, i, rest) => {
                tok(out, &format!("J{i}{}", if *rest { "r" } else { "" }));
                self.write_tm(g, x, out)?;
            }
            Tm::Field(x, c, i) => {
                tok(out, &format!("F{i}"));
                tok(out, &self.con_name(g, c.0));
                self.write_tm(g, x, out)?;
            }
            Tm::TyConApp(x, ts) => {
                tok(out, &format!("TA{}", ts.len()));
                tok(out, &self.ty_name(g, x.0));
                for t in ts {
                    self.write_tm(g, t, out)?;
                }
            }
            Tm::ConApp(c, ts) => {
                tok(out, &format!("CA{}", ts.len()));
                tok(out, &self.con_name(g, c.0));
                for t in ts {
                    self.write_tm(g, t, out)?;
                }
            }
            Tm::PrimApp(op, ts) => {
                let name = match op {
                    Prim::Builtin(n) => format!("B{}", escape(n)),
                    Prim::Effect(n) => format!("X{n}"),
                    op => format!("{op:?}"),
                };
                tok(out, &format!("R{}", ts.len()));
                tok(out, &name);
                for t in ts {
                    self.write_tm(g, t, out)?;
                }
            }
            Tm::Case(x, c) => {
                tok(out, &format!("S{} {} {}", c.branches.len(), c.lits.len(), u8::from(c.default.is_some())));
                self.write_tm(g, x, out)?;
                for (con, n, b) in &c.branches {
                    tok(out, &self.con_name(g, con.0));
                    tok(out, &n.to_string());
                    self.write_tm(g, b, out)?;
                }
                for (l, b) in &c.lits {
                    tok(out, &lit_token(l));
                    self.write_tm(g, b, out)?;
                }
                if let Some(b) = &c.default {
                    self.write_tm(g, b, out)?;
                }
            }
            Tm::Known(v) => {
                let text = self.encode(&p, &v.graph, v.id, &mut Vec::new());
                tok(out, "K");
                tok(out, &escape(&text));
            }
            Tm::Error => tok(out, "!"),
        }
        Some(())
    }

    /// A term `write_tm` wrote, read into this build's numbering: `None`
    /// if it names what this build doesn't have.
    fn read_tm<'t>(&mut self, g: &Globals, toks: &mut dyn Iterator<Item = &'t str>) -> Option<Tm> {
        let t = toks.next()?;
        let mult = |s: &str| match s {
            "0" => Some(Mult::Zero),
            "1" => Some(Mult::One),
            "w" => Some(Mult::Many),
            _ => None,
        };
        let icit = |s: &str| match s {
            "e" => Some(Icit::Expl),
            "i" => Some(Icit::Impl),
            _ => None,
        };
        let def = |this: &mut Self, n: &str| this.by_name(g).defs.get(n).copied().map(DefId);
        let ty = |this: &mut Self, n: &str| this.by_name(g).tys.get(n).copied().map(TyId);
        let con = |this: &mut Self, n: &str| this.by_name(g).cons.get(n).copied().map(ConId);
        let count = |s: &str| s.parse::<usize>().ok();
        Some(match t {
            "d" => Tm::Def(def(self, toks.next()?)?),
            "T" => Tm::TyCon(ty(self, toks.next()?)?),
            "C" => Tm::Con(con(self, toks.next()?)?),
            "P" | "L" => {
                let (x, m, i) = (unescape(toks.next()?), mult(toks.next()?)?, icit(toks.next()?)?);
                if t == "P" {
                    let a = self.read_tm(g, toks)?;
                    Tm::Pi(x.into(), m, i, Rc::new(a), Rc::new(self.read_tm(g, toks)?))
                } else {
                    Tm::Lam(x.into(), m, i, Rc::new(self.read_tm(g, toks)?))
                }
            }
            "A" => {
                let (i, m) = (icit(toks.next()?)?, mult(toks.next()?)?);
                let f = self.read_tm(g, toks)?;
                Tm::App(Rc::new(f), Rc::new(self.read_tm(g, toks)?), i, m)
            }
            "E" => {
                let (x, m) = (unescape(toks.next()?), mult(toks.next()?)?);
                let ty = self.read_tm(g, toks)?;
                let v = self.read_tm(g, toks)?;
                Tm::Let(x.into(), m, Rc::new(ty), Rc::new(v), Rc::new(self.read_tm(g, toks)?))
            }
            "K" => {
                let (k, root) = self.read_known(g, &unescape(toks.next()?))?;
                Tm::Known(Value::new(k, root))
            }
            "!" => Tm::Error,
            _ => {
                let (tag, rest) = t.split_at(t.find(|c: char| c.is_ascii_digit() || c == '-').unwrap_or(t.len()));
                let many = |this: &mut Self, n: usize, toks: &mut dyn Iterator<Item = &'t str>| -> Option<Vec<Tm>> { (0..n).map(|_| this.read_tm(g, toks)).collect() };
                match tag {
                    "v" => Tm::Var(count(rest)?),
                    "u" => Tm::Univ(rest.parse().ok()?),
                    "n" | "N" | "s" | "y" => Tm::Lit(read_lit(t)?),
                    "U" => Tm::Tuple(many(self, count(rest)?, toks)?),
                    "Y" => Tm::TupleTy(many(self, count(rest)?, toks)?),
                    "J" => {
                        let (i, r) = rest.strip_suffix('r').map_or((rest, false), |i| (i, true));
                        Tm::Proj(Rc::new(self.read_tm(g, toks)?), count(i)?, r)
                    }
                    "F" => {
                        let c = con(self, toks.next()?)?;
                        Tm::Field(Rc::new(self.read_tm(g, toks)?), c, count(rest)?)
                    }
                    "TA" => {
                        let x = ty(self, toks.next()?)?;
                        Tm::TyConApp(x, many(self, count(rest)?, toks)?)
                    }
                    "CA" => {
                        let c = con(self, toks.next()?)?;
                        Tm::ConApp(c, many(self, count(rest)?, toks)?)
                    }
                    "R" => {
                        let name = toks.next()?;
                        let op = if let Some(n) = name.strip_prefix('B') {
                            Prim::Builtin(unescape(n).into())
                        } else if let Some(n) = name.strip_prefix('X') {
                            Prim::Effect(n.parse().ok()?)
                        } else {
                            prim_named(name)?
                        };
                        Tm::PrimApp(op, many(self, count(rest)?, toks)?)
                    }
                    "S" => {
                        let (nb, nl, nd) = (count(rest)?, count(toks.next()?)?, toks.next()? == "1");
                        let x = self.read_tm(g, toks)?;
                        let mut c = CaseTm { branches: Vec::new(), lits: Vec::new(), default: None };
                        for _ in 0..nb {
                            let k = con(self, toks.next()?)?;
                            let n = count(toks.next()?)?;
                            c.branches.push((k, n, self.read_tm(g, toks)?));
                        }
                        for _ in 0..nl {
                            let l = read_lit(toks.next()?)?;
                            c.lits.push((l, self.read_tm(g, toks)?));
                        }
                        if nd {
                            c.default = Some(self.read_tm(g, toks)?);
                        }
                        Tm::Case(Rc::new(x), Rc::new(c))
                    }
                    _ => return None,
                }
            }
        })
    }

    /// The weak-head normal form kept under `key` (`force_kept`): the fuel
    /// computing it took, and its term.
    fn recall_whnf(&mut self, g: &Globals, key: &str) -> Option<(u64, Tm)> {
        if let Some(r) = self.whnfs.get(key) {
            return Some(r.clone());
        }
        let text = Self::read(key)?;
        let (steps, rest) = text.strip_prefix("whnf ")?.split_once('\n')?;
        let steps = steps.parse().ok()?;
        let mut toks = rest.split(' ').filter(|t| !t.is_empty());
        let t = self.read_tm(g, &mut toks)?;
        toks.next().is_none().then_some(())?;
        self.whnfs.insert(key.to_string(), (steps, t.clone()));
        Some((steps, t))
    }

    /// Keep weak-head normal form `t` under `key`, which took `steps` of
    /// fuel, if it can be kept.
    fn store_whnf(&mut self, g: &Globals, key: &str, steps: u64, t: &Tm) {
        let mut text = format!("whnf {steps}\n");
        if self.write_tm(g, t, &mut text).is_some() {
            Self::write(key, &text);
            self.whnfs.insert(key.to_string(), (steps, t.clone()));
        }
    }
}

/// Is `it` a definition not checked yet, whose body is still to come (a
/// builtin's is none, once its module is checked)?
fn unchecked(g: &Globals, it: Item) -> bool {
    matches!(it, Item::Def(d) if g.defs.get(d as usize).is_some_and(|i| i.body.is_none() && !i.opaque))
}

fn unescape(s: &str) -> String {
    s.replace("%20", " ").replace("%0A", "\n").replace("%25", "%")
}

fn lit_token(l: &Lit) -> String {
    match l {
        Lit::Num(n) => format!("n{n}"),
        Lit::Big(b) => format!("N{b}"),
        Lit::Str(s) => format!("s{}", hex(s.as_bytes())),
        Lit::Bytes(b) => format!("y{}", hex(b)),
    }
}

fn read_lit(t: &str) -> Option<Lit> {
    let (tag, rest) = t.split_at(1);
    Some(match tag {
        "n" => Lit::Num(rest.parse().ok()?),
        "N" => Lit::Big(Rc::new(rest.parse().ok()?)),
        "s" => Lit::Str(String::from_utf8(unhex(rest)?).ok()?.into()),
        "y" => Lit::Bytes(unhex(rest)?.into()),
        _ => return None,
    })
}

/// The primitive written as its name (`Debug`), other than those that carry
/// a value.
fn prim_named(s: &str) -> Option<Prim> {
    use Prim::*;
    [Add, Sub, Mul, Div, Rem, Neg, Eq, Ne, Lt, Le, Gt, Ge, Concat, Len, Index, Par, When, Forall].into_iter().find(|p| format!("{p:?}") == s)
}

/// How many unfoldings a value of the type checker's own evaluation takes
/// before it is kept across builds (§8.9): one that takes fewer is computed
/// again, which is quicker than looking it up.
pub const KEEP_STEPS: u64 = 1000;

/// `force` of a call, keeping its weak-head normal form across builds when
/// it is closed and takes `KEEP_STEPS` unfoldings or more (§8.9). It is
/// first computed within `KEEP_STEPS`; one that needs more is looked up,
/// and computed again from the start if it isn't kept. The value read back
/// takes from the fuel what computing it took, so whether a program checks
/// never depends on what is kept.
#[inline(never)]
pub fn force_kept(g: &Globals, v: Val) -> Val {
    let fuel = g.fuel.get();
    g.keeping.set(false);
    let outer = g.unfolds_left.replace(KEEP_STEPS);
    let r = unfold_all(g, v.clone());
    let left = g.unfolds_left.replace(outer);
    let r = if left > 0 {
        r
    } else {
        g.fuel.set(fuel);
        force_long(g, v, fuel)
    };
    g.keeping.set(true);
    r
}

/// `force_kept` of a value that takes `KEEP_STEPS` unfoldings or more,
/// with `fuel` left.
fn force_long(g: &Globals, v: Val, fuel: u64) -> Val {
    let input = closed(g, &v).then(|| quietly(g, || quote(g, 0, &v)));
    let key = input.as_ref().and_then(|t| g.known_disk.borrow_mut().whnf_key(g, t));
    if let Some(key) = &key {
        let kept = g.known_disk.borrow_mut().recall_whnf(g, key);
        if let Some((spent, t)) = kept.filter(|(spent, _)| *spent < fuel) {
            let r = quietly(g, || eval(g, &Env::new(), &t));
            g.fuel.set(fuel - spent);
            return r;
        }
        if std::env::var_os("CHECKERS_KNOWN_TRACE").is_some() {
            eprintln!("known value computed: {}", crate::core::show(g, &[], input.as_ref().unwrap()));
        }
    }
    let r = unfold_all(g, v);
    let left = g.fuel.get();
    // A computation that ran out of fuel isn't finished: not kept.
    if let (Some(key), true) = (&key, left > 0) {
        let t = quietly(g, || quote(g, 0, &r));
        g.known_disk.borrow_mut().store_whnf(g, key, fuel - left, &t);
    }
    r
}

/// `f` run with no fuel, so it unfolds nothing (quoting a value, or
/// evaluating a term read back): it takes none.
fn quietly<T>(g: &Globals, f: impl FnOnce() -> T) -> T {
    let saved = g.fuel.replace(0);
    let r = f();
    g.fuel.set(saved);
    r
}

/// Is `v` closed: no variables, and no unknowns (whose solutions would
/// change it)? Within a bound on the values looked at, since closures'
/// environments may share them; beyond it, taken as not closed.
fn closed(g: &Globals, v: &Val) -> bool {
    fn body_closed(t: &Tm) -> bool {
        !matches!(t, Tm::Meta(_)) && t.all_sub(|x, _| body_closed(x))
    }
    let mut todo = vec![v.clone()];
    let mut budget = 10_000;
    let env = |todo: &mut Vec<Val>, e: &Env| todo.extend(e.iter().cloned());
    while let Some(v) = todo.pop() {
        budget -= 1;
        if budget == 0 {
            return false;
        }
        if let Val::Known(_) = v {
            continue;
        }
        match force_meta(g, v) {
            Val::Neutral(h, sp) => {
                match h {
                    Head::Var(_) | Head::Meta(_) => return false,
                    Head::Def(_) => {}
                    Head::Prim(_, args) => todo.extend(args.iter().cloned()),
                }
                for e in sp.iter() {
                    match e {
                        Elim::App(a, _) => todo.push(a.clone()),
                        Elim::Proj(..) | Elim::Field(..) => {}
                        Elim::Case(c, e) => {
                            let bodies = c.branches.iter().map(|b| &b.2).chain(c.lits.iter().map(|b| &b.1)).chain(c.default.iter());
                            if !bodies.into_iter().all(body_closed) {
                                return false;
                            }
                            env(&mut todo, e);
                        }
                    }
                }
            }
            Val::Lam(_, _, _, c) | Val::Pi(_, _, _, _, c) if !body_closed(&c.body) => return false,
            Val::Lam(_, _, _, c) => env(&mut todo, &c.env),
            Val::Pi(_, _, _, a, c) => {
                todo.push((*a).clone());
                env(&mut todo, &c.env);
            }
            Val::TyCon(_, xs) | Val::Con(_, xs) | Val::TupleTy(xs) | Val::Tuple(xs) => todo.extend(xs.iter().cloned()),
            Val::Univ(_) | Val::Lit(_) | Val::Known(_) | Val::Error => {}
        }
    }
    true
}

/// Keep `bytes` under `key`: whole or not at all, written elsewhere, then
/// renamed.
fn write_file(key: &str, bytes: &[u8]) {
    let Some(dir) = dir() else { return };
    if std::fs::create_dir_all(&dir).is_err() {
        return;
    }
    let tmp = dir.join(format!("{key}.{}", std::process::id()));
    if std::fs::write(&tmp, bytes).is_ok() {
        let _ = std::fs::rename(&tmp, dir.join(key));
    }
}

/// The start of a file of static data.
const STATIC_HEADER: &[u8] = b"checkers static 1\n";

fn varint(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push(x as u8 | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}

fn blob(out: &mut Vec<u8>, b: &[u8]) {
    varint(out, b.len() as u64);
    out.extend_from_slice(b);
}

/// Reads what `varint` and `blob` write.
struct Reader<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn byte(&mut self) -> Option<u8> {
        let x = *self.b.get(self.at)?;
        self.at += 1;
        Some(x)
    }

    fn varint(&mut self) -> Option<u64> {
        let mut x = 0u64;
        for shift in (0..64).step_by(7) {
            let b = self.byte()?;
            x |= ((b & 0x7f) as u64) << shift;
            if b < 0x80 {
                return Some(x);
            }
        }
        None
    }

    fn blob(&mut self) -> Option<&'a [u8]> {
        let n = self.varint()? as usize;
        let b = self.b.get(self.at..self.at.checked_add(n)?)?;
        self.at += n;
        Some(b)
    }
}
