//! Known values kept across builds (§8.9), in `.checkers/known/` beside the
//! checked file, as Z3's answers are (D100): those native code computes for
//! the type checker, and those folding computes in native code.
//!
//! A value is stored under a key: a digest of the term computed, its type,
//! the `ckc` executable, and every definition and type the computation can
//! reach, transitively. A definition counts by its type and body (sealed
//! bodies too), a type by its parameters and constructors. So editing a
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

use crate::core::{Globals, Lit, Tm};
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
            let next = ["DefId(", "TyId(", "ConId("].iter().filter_map(|p| rest.find(p).map(|i| (i, *p))).min();
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
                let (opaque, sealed, comptime) = (info.opaque, info.sealed, format!("{:?}", info.comptime));
                let ty = self.render(p, &ty, &mut deps);
                let body = match &body {
                    Some(b) => self.render(p, b, &mut deps),
                    // A builtin: the runtime's code, which the executable covers.
                    None => "builtin".into(),
                };
                format!("def {}\nty {ty}\nbody {body}\nopaque {opaque} sealed {sealed} comptime {comptime}", self.def_name(p, d))
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
        self.items.insert(it, r.clone());
        r
    }

    /// A digest of `it` and every item it reaches, each by name and digest.
    fn closure(&mut self, p: &Program, it: Item) -> String {
        if let Some(c) = self.closures.get(&it) {
            return c.clone();
        }
        let mut todo = vec![it];
        let mut seen = HashSet::new();
        let mut parts = Vec::new();
        while let Some(x) = todo.pop() {
            if !seen.insert(x) {
                continue;
            }
            let (d, deps) = self.item(p, x);
            let name = match x {
                Item::Def(d) => format!("def {}", self.def_name(p, d)),
                Item::Ty(t) => format!("ty {}", self.ty_name(p.g, t)),
            };
            parts.push(format!("{name} {d}"));
            todo.extend(deps);
        }
        parts.sort();
        let c = crate::verify::digest(&parts.join("\n"));
        self.closures.insert(it, c.clone());
        c
    }

    /// A key over `text` and everything `items` reach.
    fn key_of(&mut self, p: &Program, text: &str, mut items: Vec<Item>) -> String {
        items.sort();
        items.dedup();
        let mut parts: Vec<String> = items.into_iter().map(|it| self.closure(p, it)).collect();
        parts.sort();
        let content = format!("{HEADER}\n{}\n{text}\n{}", crate::verify::tool_identity(), parts.join("\n"));
        crate::verify::digest(&content)
    }

    /// The key of `t` at type `ty`: what the module comment says.
    pub fn key(&mut self, g: &Globals, t: &Tm, ty: Option<&Tm>) -> String {
        let p = Program::of(g);
        let mut items = Vec::new();
        let term = self.render(&p, t, &mut items);
        let ty = ty.map(|ty| self.render(&p, ty, &mut items)).unwrap_or_default();
        self.key_of(&p, &format!("{term}\n{ty}"), items)
    }

    /// The key of closed code `ir` that folding computes, in program `p`:
    /// `None` if it has a part a name can't say.
    pub fn code_key(&mut self, p: &Program, ir: &Ir) -> Option<String> {
        let mut items = Vec::new();
        let mut text = String::from("folded ");
        self.ir_text(p, ir, &mut text, &mut items)?;
        Some(self.key_of(p, &text, items))
    }

    /// Constructors by name, for reading a stored value.
    fn by_name(&mut self, g: &Globals) -> &ByName {
        if self.by_name.as_ref().is_none_or(|b| b.defs_len != g.defs.len() || b.tys_len != g.tys.len()) {
            let p = Program::of(g);
            let defs = (0..g.defs.len() as u32).map(|d| (self.def_name(&p, d), d)).collect();
            let cons = (0..g.cons.len() as u32).map(|c| (self.con_name(g, c), c)).collect();
            self.by_name = Some(ByName { defs_len: g.defs.len(), tys_len: g.tys.len(), defs, cons });
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
        term_of(Arc::new(b.finish()), root)
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
