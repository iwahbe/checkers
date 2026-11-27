//! Known values kept across builds (§8.9), in `.checkers/known/` beside the
//! checked file, as Z3's answers are (D100).
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

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use crate::core::{Globals, Lit, Tm};
use crate::known::{Builder, Code, Known, Node, Value};

const HEADER: &str = "checkers known 1";

/// What a key covers besides the term: a definition or a type (with its
/// constructors).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Item {
    Def(u32),
    Ty(u32),
}

/// Names and digests, worked out once per program.
#[derive(Default)]
pub struct KnownCache {
    def_names: HashMap<u32, String>,
    ty_names: HashMap<u32, String>,
    /// Each item's digest and the items it mentions.
    items: HashMap<Item, (String, Vec<Item>)>,
    /// From names back to numbers, for reading a stored value: built when
    /// first needed, again if more have been declared since.
    by_name: Option<(usize, usize, HashMap<String, u32>, HashMap<String, u32>)>,
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
    (s.len() % 2 == 0).then_some(())?;
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
    fn def_name(&mut self, g: &Globals, d: u32) -> String {
        if let Some(n) = self.def_names.get(&d) {
            return n.clone();
        }
        let info = &g.defs[d as usize];
        let k = g.defs[..d as usize].iter().filter(|i| i.module == info.module && i.name == info.name).count();
        let n = escape(&format!("{}.{}#{k}", info.module, info.name));
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
    fn encode(&mut self, g: &Globals, k: &Known, root: u32, items: &mut Vec<Item>) -> String {
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
                    format!("fd {}", self.def_name(g, d.0))
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

    /// `t`'s `Debug` form with every number naming a definition, type or
    /// constructor replaced by its name, and each known value by a digest
    /// of its form written with names; the items it names are added to
    /// `items`.
    fn render(&mut self, g: &Globals, t: &Tm, items: &mut Vec<Item>) -> String {
        fn strip(c: &mut KnownCache, g: &Globals, t: &Tm, items: &mut Vec<Item>) -> Tm {
            match t {
                Tm::Known(v) => {
                    let text = c.encode(g, &v.graph, v.id, items);
                    Tm::Lit(Lit::Str(Rc::from(format!("\0known {}", crate::verify::digest(&text)))))
                }
                _ => t.map_sub(|x, _| strip(c, g, x, items)),
            }
        }
        let s = format!("{:?}", strip(self, g, t, items));
        self.rename(g, &s, items)
    }

    fn rename(&mut self, g: &Globals, s: &str, items: &mut Vec<Item>) -> String {
        let mut out = String::with_capacity(s.len());
        let mut rest = s;
        loop {
            let next = ["DefId(", "TyId(", "ConId("].iter().filter_map(|p| rest.find(p).map(|i| (i, *p))).min();
            let Some((i, p)) = next else {
                out += rest;
                return out;
            };
            out += &rest[..i];
            let after = &rest[i + p.len()..];
            let digits = after.chars().take_while(|c| c.is_ascii_digit()).count();
            let n: Option<u32> = after[..digits].parse().ok();
            match (n, after[digits..].starts_with(')')) {
                (Some(n), true) => {
                    let name = match p {
                        "DefId(" if (n as usize) < g.defs.len() => {
                            items.push(Item::Def(n));
                            format!("def {}", self.def_name(g, n))
                        }
                        "TyId(" if (n as usize) < g.tys.len() => {
                            items.push(Item::Ty(n));
                            format!("ty {}", self.ty_name(g, n))
                        }
                        "ConId(" if (n as usize) < g.cons.len() => {
                            items.push(Item::Ty(g.cons[n as usize].ty.0));
                            format!("con {}", self.con_name(g, n))
                        }
                        _ => format!("{p}{n})"),
                    };
                    out += &format!("<{name}>");
                    rest = &after[digits + 1..];
                }
                _ => {
                    out += p;
                    rest = after;
                }
            }
        }
    }

    /// An item's digest, and the items its text names.
    fn item(&mut self, g: &Globals, it: Item) -> (String, Vec<Item>) {
        if let Some(r) = self.items.get(&it) {
            return r.clone();
        }
        let mut deps = Vec::new();
        let text = match it {
            Item::Def(d) => {
                let info = &g.defs[d as usize];
                let (ty, body) = (info.ty.clone(), info.body.clone());
                let (opaque, sealed, comptime) = (info.opaque, info.sealed, format!("{:?}", info.comptime));
                let ty = self.render(g, &ty, &mut deps);
                let body = match &body {
                    Some(b) => self.render(g, b, &mut deps),
                    // A builtin: the runtime's code, which the executable covers.
                    None => "builtin".into(),
                };
                format!("def {}\nty {ty}\nbody {body}\nopaque {opaque} sealed {sealed} comptime {comptime}", self.def_name(g, d))
            }
            Item::Ty(t) => {
                let info = &g.tys[t as usize];
                let params = info.params.clone();
                let ctors = info.ctors.clone();
                let flags = format!("record {} abstract {} positive {:?} negative {:?} dicts {}", info.is_record, info.is_abstract, info.positive, info.negative, info.dicts);
                let mut text = format!("ty {}\n{flags}\n", self.ty_name(g, t));
                for (x, p) in &params {
                    text += &format!("param {x} {}\n", self.render(g, p, &mut deps));
                }
                for c in ctors {
                    let con = &g.cons[c.0 as usize];
                    let (tag, fields) = (con.tag, con.fields.clone());
                    text += &format!("con {} {tag}\n", self.con_name(g, c.0));
                    for (x, m, i, f) in &fields {
                        text += &format!("field {x} {m:?} {i:?} {}\n", self.render(g, f, &mut deps));
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

    /// The key of `t` at type `ty`: what the module comment says.
    pub fn key(&mut self, g: &Globals, t: &Tm, ty: Option<&Tm>) -> String {
        let mut todo = Vec::new();
        let term = self.render(g, t, &mut todo);
        let ty = ty.map(|ty| self.render(g, ty, &mut todo)).unwrap_or_default();
        let mut seen = HashSet::new();
        let mut parts = Vec::new();
        while let Some(it) = todo.pop() {
            if !seen.insert(it) {
                continue;
            }
            let (d, deps) = self.item(g, it);
            let name = match it {
                Item::Def(d) => format!("def {}", self.def_name(g, d)),
                Item::Ty(t) => format!("ty {}", self.ty_name(g, t)),
            };
            parts.push(format!("{name} {d}"));
            todo.extend(deps);
        }
        parts.sort();
        let content = format!("{HEADER}\n{}\n{term}\n{ty}\n{}", crate::verify::tool_identity(), parts.join("\n"));
        crate::verify::digest(&content)
    }

    /// The value stored under `key`, read into this build's numbering.
    pub fn recall(&mut self, g: &Globals, key: &str) -> Option<Tm> {
        let text = std::fs::read_to_string(dir()?.join(key)).ok()?;
        let mut lines = text.lines();
        (lines.next()? == HEADER).then_some(())?;
        if self.by_name.as_ref().is_none_or(|(d, t, _, _)| *d != g.defs.len() || *t != g.tys.len()) {
            let defs = (0..g.defs.len() as u32).map(|d| (self.def_name(g, d), d)).collect();
            let cons = (0..g.cons.len() as u32).map(|c| (self.con_name(g, c), c)).collect();
            self.by_name = Some((g.defs.len(), g.tys.len(), defs, cons));
        }
        let (_, _, defs, cons) = self.by_name.as_ref()?;
        let mut b = Builder::default();
        let mut ids: Vec<u32> = Vec::new();
        for l in lines {
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
        let Some(dir) = dir() else { return };
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
        let text = format!("{HEADER}\n{}", self.encode(g, &k, root, &mut Vec::new()));
        if std::fs::create_dir_all(&dir).is_err() {
            return;
        }
        // Whole or not at all: written elsewhere, then renamed.
        let tmp = dir.join(format!("{key}.{}", std::process::id()));
        if std::fs::write(&tmp, text).is_ok() {
            let _ = std::fs::rename(&tmp, dir.join(key));
        }
    }
}
