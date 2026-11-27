//! Translation of an obligation to SMT-LIB 2 (SPEC §7.3).
//!
//! Every term is translated together with its sort. Sorts only depend on type
//! arguments, never on values, so a dependent family such as `Parsed a src k`
//! becomes the parametric datatype `Parsed a`. Functions defined in the module
//! (and imported `transparent` ones) are reflected as `define-fun-rec`,
//! instantiated per type; others are uninterpreted. Every application of a
//! function with a postcondition contributes that postcondition (#538).

use crate::core::{eval, force, max_var, quote, CaseTm, ConId, DefId, Lit, Mult, Prim, Tm, TyId, Val};
use crate::elab::{has_meta, Elab, ObLocal, Obligation};
use super::Sx;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

/// Why an obligation can't be sent to the solver (E0451).
#[derive(Debug, Clone)]
pub struct Outside(pub String);

/// What a term with a type error is outside the fragment for (§7.3).
const TYPE_ERROR: &str = "code with a type error";

impl Outside {
    /// Code with a type error: an elaborated error, or a term whose parts
    /// don't have the sorts its place needs. Never given to Z3 (§7.3).
    pub fn type_error() -> Outside {
        Outside(TYPE_ERROR.into())
    }

    pub fn is_type_error(&self) -> bool {
        self.0 == TYPE_ERROR
    }
}

type Tx<T> = Result<T, Outside>;

fn out<T>(why: impl Into<String>) -> Tx<T> {
    Err(Outside(why.into()))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    Int,
    Bool,
    Str,
    /// An array (#624): a sequence of its elements' sort.
    Seq(Box<Sort>),
    /// A multiset of elements of a sort: counts (#553, #625).
    Bag(Box<Sort>),
    /// A datatype with its type arguments.
    Data(TyId, Vec<Sort>),
    Tuple(Vec<Sort>),
    /// An uninterpreted sort: an abstract type or a type variable.
    Unin(String, Vec<Sort>),
    /// A function value (#630): Z3's array from its parameter's sort to its
    /// result's, curried (`Int -> Int -> Int` is an array of arrays), so a
    /// partial application is a value too; applying it is `select`, a
    /// lambda is a `lambda`.
    Fun(Box<Sort>, Box<Sort>),
}

/// The SMT name of a program symbol (a function, constant, local, datatype,
/// constructor, field or sort): its name, quoted, after a `#`. Z3's names
/// are simple symbols (SMT-LIB §3.1), which never have a `#`, so a
/// program's `seq.unit` is never Z3's.
fn sym(s: &str) -> String {
    format!("|#{}|", s.replace('|', "_"))
}

/// The recognizer Z3 makes for the constructor or stand-in named `con` (a
/// `sym`): `is-` before its name.
fn is_sym(con: &str) -> String {
    format!("|is-{}|", con.trim_matches('|'))
}

impl Sort {
    /// Whether the uninterpreted sort named `n` occurs in this one.
    fn mentions(&self, n: &str) -> bool {
        match self {
            Sort::Int | Sort::Bool | Sort::Str => false,
            Sort::Seq(x) | Sort::Bag(x) => x.mentions(n),
            Sort::Data(_, args) | Sort::Tuple(args) => args.iter().any(|a| a.mentions(n)),
            Sort::Unin(m, args) => m == n || args.iter().any(|a| a.mentions(n)),
            Sort::Fun(p, r) => p.mentions(n) || r.mentions(n),
        }
    }

    fn render(&self, e: &Elab) -> String {
        match self {
            Sort::Int => "Int".into(),
            Sort::Bool => "Bool".into(),
            // A string is its UTF-8 bytes (§7.3): `++`, `len` and `utf8.encode`
            // are then native, and literals are byte sequences.
            Sort::Str => "(Seq Int)".into(),
            Sort::Seq(x) => format!("(Seq {})", x.render(e)),
            Sort::Bag(x) => format!("(Array {} Int)", x.render(e)),
            Sort::Data(t, args) => apply_sort(ty_sym(e, *t), args, e),
            Sort::Tuple(args) => apply_sort(tuple_sym(args.len()), args, e),
            Sort::Unin(n, args) => apply_sort(sym(n), args, e),
            Sort::Fun(p, r) => format!("(Array {} {})", p.render(e), r.render(e)),
        }
    }
}

fn apply_sort(head: String, args: &[Sort], e: &Elab) -> String {
    if args.is_empty() {
        head
    } else {
        format!("({head} {})", args.iter().map(|a| a.render(e)).collect::<Vec<_>>().join(" "))
    }
}

fn ty_sym(e: &Elab, t: TyId) -> String {
    let ti = &e.g.tys[t.0 as usize];
    sym(&format!("{}.{}", ti.module, ti.name))
}

pub(crate) fn con_sym(e: &Elab, c: ConId) -> String {
    let ci = &e.g.cons[c.0 as usize];
    let ti = &e.g.tys[ci.ty.0 as usize];
    sym(&format!("{}.{}", ti.module, ci.name))
}

/// The recognizer of constructor `c`. Z3 names it `is-C` and resolves it by
/// its argument's sort; `(_ is C)` is ambiguous once a parametric datatype is
/// used at two sorts.
fn tester(e: &Elab, c: ConId) -> String {
    is_sym(&con_sym(e, c))
}

fn sel_sym(e: &Elab, c: ConId, k: usize) -> String {
    let ci = &e.g.cons[c.0 as usize];
    let ti = &e.g.tys[ci.ty.0 as usize];
    sym(&format!("{}.{}.{}", ti.module, ci.name, k))
}

/// A stand-in constructor without fields, added to a datatype Z3 would
/// otherwise reject as not well-founded: one whose values all reach the type
/// again through an array or a function (`Cells cells : cells~Array Grid`,
/// `FromEmpty f : f~(Empty -> Absurd)`). Z3 doesn't count an empty array as a
/// base. The program can't build it, so it only adds values the solver must
/// consider; no value the program names is one (`real_values`).
fn base_sym(e: &Elab, id: TyId) -> String {
    let ti = &e.g.tys[id.0 as usize];
    sym(&format!("{}.{}#base", ti.module, ti.name))
}

fn base_tester(e: &Elab, id: TyId) -> String {
    is_sym(&base_sym(e, id))
}

fn tuple_sym(n: usize) -> String {
    format!("|Tuple{n}|")
}

fn tuple_con(n: usize) -> String {
    format!("|tuple{n}|")
}

fn tuple_sel(n: usize, k: usize) -> String {
    format!("|tuple{n}.{k}|")
}

/// How many datatypes deep `value_terms` looks into a value's fields:
/// `Result (Parsed a src i) (Error src)` gives what `Parsed`'s fields say,
/// not what `Error`'s kind's do. Deeper facts made `std.json`'s proofs too
/// slow for Z3.
const DATA_DEPTH: usize = 2;

/// What a de Bruijn variable stands for during translation.
#[derive(Clone)]
enum Ent {
    /// A term of the given sort.
    Term(String, Sort),
    /// A type: the sort it denotes.
    Ty(Sort),
    /// Something the solver can't see (a value only used in types).
    Opaque(String),
    /// A known function value: a closed term (a top-level function or a
    /// lambda without free variables), keyed for instance names.
    Known(String),
    /// A type constructor not applied to its last argument (`List` for a
    /// `Functor`, M25): `\y -> T … y`, closed.
    TyFun(TyId, Vec<Sort>),
    /// A type constructor variable (`f` of kind `Type -> Type`): an
    /// uninterpreted sort of that name, applied to its arguments' sorts.
    TyVar(String),
}

impl fmt::Debug for Ent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ent::Term(t, _) => write!(f, "{t}"),
            Ent::Ty(_) => write!(f, "<type>"),
            Ent::Known(k) => write!(f, "{k}"),
            Ent::Opaque(w) => write!(f, "<{w}>"),
            Ent::TyFun(..) | Ent::TyVar(_) => write!(f, "<type constructor>"),
        }
    }
}

/// A use of a function at a sort instance.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Inst {
    def: DefId,
    tys: Vec<Sort>,
    /// Keys of known function arguments (higher-order specialization).
    funs: Vec<String>,
}

/// An application whose postcondition should be assumed.
/// A reflected instance's definition: name, `define-funs-rec` head, body.
type Defn = (String, String, String);
/// An instance's environment, parameters and result sort.
type InstSig = (Vec<Ent>, Vec<(String, Sort)>, Sort);

struct PostUse {
    def: DefId,
    env: Vec<Ent>,
    /// The result is a `Nat`: assumed where the precondition holds.
    nat: bool,
    /// What the result's type says of it (`value_terms`: `(Nat, (j~Nat, i
    /// <= j))`, `Pair Nat (j~Nat, i <= j)`), assumed too where the
    /// precondition holds.
    parts: Vec<String>,
}

/// What it takes to reflect only some definitions: the declarations that
/// aren't reflected anyway, and each reflected one (name, head, body, its
/// uninterpreted declaration).
pub struct Focus {
    others: Vec<String>,
    /// The copies of functions the group's conditions apply (`definitions`).
    copies: String,
    group: Vec<(String, String, String, Option<String>)>,
}

impl Focus {
    /// Reflect the definitions `terms` mention; leave the rest
    /// uninterpreted. `None` if that is all or none of them.
    fn mentioned_in(&self, terms: &str) -> Option<String> {
        let named: HashSet<&str> = symbols(terms).collect();
        let (on, off): (Vec<_>, Vec<_>) = self.group.iter().partition(|(n, ..)| named.contains(n.trim_matches('|')));
        if on.is_empty() || off.is_empty() {
            return None;
        }
        let mut out = String::new();
        for d in &self.others {
            out += d;
            out += "\n";
        }
        for (_, _, _, d) in &off {
            out += d.as_deref()?;
            out += "\n";
        }
        let heads: Vec<&str> = on.iter().map(|g| g.1.as_str()).collect();
        let bodies: Vec<&str> = on.iter().map(|g| g.2.as_str()).collect();
        out += &self.copies;
        out += &format!("(define-funs-rec ({}) ({}))\n", heads.join(" "), bodies.join(" "));
        Some(out)
    }
}

/// Reflected definitions, each its name, `define-funs-rec` head and body, as
/// Z3 is to be given them: the bodies, and the `define-fun`s to put before
/// them.
///
/// Z3 splits a recursive definition into cases only at an `ite` whose
/// condition applies no function of a `define-funs-rec` (`splits`), and
/// unfolds each case at an application only as the search reaches it. A
/// definition without such an `ite` is one case, which Z3 unfolds wherever the
/// function is applied, and so at the applications each unfolding makes,
/// without end: a function recursing over a sequence pattern (a `match` on
/// `uncons xs`, with `uncons` reflected), or over an `if` on `is_digit c`.
/// Whether a goal near one was proved then depended on whether Z3 met a
/// contradiction before its work limit, so on the order of the facts and how
/// they were written. So in such a definition, a condition that applies only
/// functions that don't recurse, through any number of calls, applies copies
/// of them made with `define-fun` instead, which Z3 substitutes where they
/// are used (`|uncons#cond|`); elsewhere the functions are kept, so that equal
/// arguments give equal applications at once. A condition applying a
/// recursive function is left as it is: Z3 can't split there.
///
/// A recursive call under a condition Z3 can't split (one applying a
/// recursive function, through any number of calls) is in the case of the
/// conditions above it, and Z3 unfolds the call whenever that case's guard
/// holds of the call's own arguments, by propagation alone, which its limit on
/// unfolding depth doesn't bound. A `decreasing` definition is such a case:
/// its only split is `D` (its `Nat` parameters non-negative), true again
/// of each recursive call. So such a condition is passed to a definition of
/// its own, as a parameter that Z3 splits on (`lifted`): unfolding the call
/// then waits for the search to decide the condition.
///
/// Each definition comes back as its head and body, followed by the heads
/// and bodies of the definitions lifted from it, which go wherever it does.
///
/// `cache` keeps each body as rewritten, for the other queries of the module:
/// a body is rewritten the same way in every group holding it (a group holds
/// every definition its members apply).
fn definitions(group: &[(&str, &str, &str)], cache: Option<&RefCell<Rewritten>>) -> (String, Vec<(String, String)>) {
    let index: HashMap<&str, usize> = group.iter().enumerate().map(|(k, g)| (g.0.trim_matches('|'), k)).collect();
    let calls: Vec<Vec<usize>> = group
        .iter()
        .map(|(name, _, body)| {
            let named = |s: &[String]| -> Vec<usize> {
                let mut c: Vec<usize> = s.iter().filter_map(|n| index.get(n.as_str()).copied()).collect();
                c.sort();
                c.dedup();
                c
            };
            if let Some(s) = cache.and_then(|c| c.borrow().symbols.get(*name).cloned()) {
                return named(&s);
            }
            let mut s: Vec<String> = symbols(body).map(str::to_string).collect();
            s.sort();
            s.dedup();
            let c = named(&s);
            if let Some(cache) = cache {
                cache.borrow_mut().symbols.insert(name.to_string(), Rc::new(s));
            }
            c
        })
        .collect();
    let sccs = crate::elab::order::sccs(&calls);
    let mut component = vec![0; group.len()];
    for (c, scc) in sccs.iter().enumerate() {
        for &k in scc {
            component[k] = c;
        }
    }
    let mut recursive = vec![false; group.len()];
    // Applies no recursive function, through any number of calls.
    let mut clean = vec![false; group.len()];
    // Dependencies first.
    for scc in &sccs {
        for &k in scc {
            recursive[k] = scc.len() > 1 || calls[k].contains(&k);
            clean[k] = !recursive[k] && calls[k].iter().all(|&j| clean[j]);
        }
    }
    let mut used = vec![false; group.len()];
    let bodies = group
        .iter()
        .enumerate()
        .map(|(k, (name, head, body))| {
            if !recursive[k] {
                return (head.to_string(), body.to_string());
            }
            if let Some(b) = cache.and_then(|c| c.borrow().bodies.get(*name).cloned()) {
                for n in &b.2 {
                    if let Some(&j) = index.get(n.as_str()) {
                        used[j] = true;
                    }
                }
                return (b.0, b.1);
            }
            let Some(mut x) = super::parse_sx(body).pop() else { return (head.to_string(), body.to_string()) };
            // Only a definition Z3 would make one case.
            let mut names = BTreeSet::new();
            if calls[k].iter().any(|&j| clean[j]) && !splits(&x, &index) {
                x = cond_copies(&x, &index, &clean, &mut names);
            }
            let own: HashSet<usize> = (0..group.len()).filter(|&j| component[j] == component[k]).collect();
            let mut extra = Vec::new();
            let (h, b) = match super::parse_sx(head).pop() {
                Some(Sx::List(h)) if h.len() == 3 => {
                    let mut lift = Lift { index: &index, own: &own, name: name.trim_matches('|'), head: &h, extra: &mut extra };
                    let x = lift.tail(&x, &mut Vec::new());
                    let mut heads = head.to_string();
                    let mut bodies = super::print_sx(&x);
                    for (hd, bd) in &extra {
                        heads += " ";
                        heads += &super::print_sx(hd);
                        bodies += " ";
                        bodies += &super::print_sx(bd);
                    }
                    (heads, bodies)
                }
                _ => (head.to_string(), super::print_sx(&x)),
            };
            // Unchanged, the text as it was.
            let b = if names.is_empty() && h == *head { body.to_string() } else { b };
            let names = names.into_iter().collect::<Vec<String>>();
            if let Some(c) = cache {
                c.borrow_mut().bodies.insert(name.to_string(), (h.clone(), b.clone(), names.clone()));
            }
            for n in &names {
                if let Some(&j) = index.get(n.as_str()) {
                    used[j] = true;
                }
            }
            (h, b)
        })
        .collect();
    // The copies the conditions apply, and those they apply.
    let mut need = vec![false; group.len()];
    let mut stack: Vec<usize> = (0..group.len()).filter(|&k| used[k]).collect();
    while let Some(k) = stack.pop() {
        if !need[k] {
            need[k] = true;
            stack.extend(calls[k].iter().copied());
        }
    }
    let mut copies = String::new();
    for &k in sccs.iter().flatten().filter(|&&k| need[k]) {
        let (name, head, body) = group[k];
        let text = match cache.and_then(|c| c.borrow().copies.get(name).cloned()) {
            Some(t) => t,
            None => {
                // `(name (params) sort)` → `(define-fun name#cond (params) sort body)`, its
                // applications of the group's functions made the copies'.
                let rename = |t: &str| {
                    let mut out = String::with_capacity(t.len());
                    for (i, part) in t.split('|').enumerate() {
                        if i > 0 {
                            out.push('|');
                        }
                        out.push_str(part);
                        if i % 2 == 1 && index.contains_key(part) {
                            out.push_str("#cond");
                        }
                    }
                    out
                };
                let t = format!("(define-fun {} {})\n", rename(&head[1..head.len() - 1]), rename(body));
                if let Some(c) = cache {
                    c.borrow_mut().copies.insert(name.to_string(), t.clone());
                }
                t
            }
        };
        copies += &text;
    }
    (copies, bodies)
}

/// Z3 splits a definition `x` into cases (as `compute_cases` in Z3's
/// `recfun_decl_plugin.cpp` does): looking from the top, through
/// applications, it finds an `ite` whose condition applies no function of the
/// group, and one of whose branches does. An `ite` whose condition applies
/// one is kept whole, and not looked into.
fn splits(x: &Sx, index: &HashMap<&str, usize>) -> bool {
    let Sx::List(items) = x else { return false };
    if is_binder(items) {
        return false;
    }
    if items.len() == 4 && matches!(&items[0], Sx::Atom(a) if a == "ite") {
        let mut applied = Vec::new();
        applies(&items[1], index, &mut applied);
        if !applied.is_empty() {
            return false;
        }
        let (mut t, mut e) = (Vec::new(), Vec::new());
        applies(&items[2], index, &mut t);
        applies(&items[3], index, &mut e);
        return !t.is_empty() || !e.is_empty();
    }
    items.iter().any(|y| splits(y, index))
}

/// Bodies rewritten by `definitions`, and the copies of functions it made:
/// the same in each query of a module.
#[derive(Default)]
pub struct Rewritten {
    /// A function's head and body, rewritten, each followed by those of the
    /// definitions lifted from it, and the functions whose copies it
    /// applies, by its name.
    bodies: HashMap<String, (String, String, Vec<String>)>,
    /// A function's copy, by its name.
    copies: HashMap<String, String>,
    /// The symbols a body names, by its function's name.
    symbols: HashMap<String, Rc<Vec<String>>>,
}

/// The `|quoted|` symbols of SMT-LIB text: every definition's name is one.
fn symbols(text: &str) -> impl Iterator<Item = &str> {
    text.split('|').skip(1).step_by(2)
}

/// `x` with each condition of its `ite`s that applies functions of the
/// group (outside `lambda`s and quantifiers, which Z3 doesn't look into), all
/// `clean`, applying their copies instead. `names` gathers those functions.
fn cond_copies(x: &Sx, index: &HashMap<&str, usize>, clean: &[bool], names: &mut BTreeSet<String>) -> Sx {
    match x {
        Sx::List(items) if is_binder(items) => x.clone(),
        Sx::List(items) if items.len() == 4 && matches!(&items[0], Sx::Atom(a) if a == "ite") => {
            let mut applied = Vec::new();
            applies(&items[1], index, &mut applied);
            let cond = if !applied.is_empty() && applied.iter().all(|&k| clean[k]) {
                renamed(&items[1], index, names)
            } else {
                items[1].clone()
            };
            Sx::List(vec![
                items[0].clone(),
                cond,
                cond_copies(&items[2], index, clean, names),
                cond_copies(&items[3], index, clean, names),
            ])
        }
        Sx::List(items) => Sx::List(items.iter().map(|y| cond_copies(y, index, clean, names)).collect()),
        Sx::Atom(_) => x.clone(),
    }
}

/// `binder` (`lam` or `all` followed by a mark) is named by height: one
/// more than the greatest of the binders inside it, and 0 if there are none,
/// so a term is spelled the same wherever it occurs in a query, whatever it is
/// inside. The binders of the lambdas and `forall`s around it are still marks,
/// so none is captured: a binder's height is greater than those inside it.
fn name_binders(text: &str, mark: &str) -> String {
    let mut height = 0;
    for prefix in ["|lam", "|all"] {
        let mut rest = text;
        while let Some(k) = rest.find(prefix) {
            rest = &rest[k + prefix.len()..];
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            if digits > 0 && rest[digits..].starts_with('.') {
                height = height.max(rest[..digits].parse::<usize>().unwrap_or(0) + 1);
            }
        }
    }
    text.replace(&format!("|lam{mark}."), &format!("|lam{height}.")).replace(&format!("|all{mark}."), &format!("|all{height}."))
}

/// A `lambda`, `forall` or `exists`.
fn is_binder(items: &[Sx]) -> bool {
    matches!(items.first(), Some(Sx::Atom(a)) if a == "lambda" || a == "forall" || a == "exists")
}

/// The functions of the group `x` applies, outside `lambda`s and quantifiers.
fn applies(x: &Sx, index: &HashMap<&str, usize>, out: &mut Vec<usize>) {
    match x {
        Sx::Atom(a) => out.extend(index.get(a.trim_matches('|'))),
        Sx::List(items) if is_binder(items) => {}
        Sx::List(items) => items.iter().for_each(|y| applies(y, index, out)),
    }
}

/// `x` applying the copies of the group's functions, outside `lambda`s and
/// quantifiers.
fn renamed(x: &Sx, index: &HashMap<&str, usize>, names: &mut BTreeSet<String>) -> Sx {
    match x {
        Sx::Atom(a) if index.contains_key(a.trim_matches('|')) => {
            let n = a.trim_matches('|');
            names.insert(n.to_string());
            Sx::Atom(format!("|{n}#cond|"))
        }
        Sx::Atom(_) => x.clone(),
        Sx::List(items) if is_binder(items) => x.clone(),
        Sx::List(items) => Sx::List(items.iter().map(|y| renamed(y, index, names)).collect()),
    }
}

/// Lifting a recursive definition's conditions that Z3 can't split
/// (`definitions`): the group's names, the definition's component's, the
/// definition's name and head, and the lifted definitions made so far (head,
/// body).
struct Lift<'a> {
    index: &'a HashMap<&'a str, usize>,
    own: &'a HashSet<usize>,
    name: &'a str,
    head: &'a [Sx],
    extra: &'a mut Vec<(Sx, Sx)>,
}

impl Lift<'_> {
    fn params(&self) -> Vec<&Sx> {
        match &self.head[1] {
            Sx::List(ps) => ps.iter().filter_map(|p| if let Sx::List(p) = p { p.first() } else { None }).collect(),
            Sx::Atom(_) => Vec::new(),
        }
    }

    /// Would Z3 unfold, by propagation alone, a recursive call under `x` (an
    /// `ite` whose condition it can't split) whenever it unfolds this case,
    /// whose split conditions are `path`? It does where the case's guard holds
    /// of the call's arguments as soon as of the parameters: the definition
    /// has no split, or the call is to the definition itself and each of
    /// `path` names only parameters the call passes unchanged.
    fn stuck(&self, x: &[Sx], path: &[Sx]) -> bool {
        if !(x.len() == 4 && matches!(&x[0], Sx::Atom(a) if a == "ite")) {
            return false;
        }
        let mut c = Vec::new();
        applies(&x[1], self.index, &mut c);
        if c.is_empty() {
            return false;
        }
        if path.is_empty() {
            let mut b = Vec::new();
            applies(&x[2], self.index, &mut b);
            applies(&x[3], self.index, &mut b);
            return b.iter().any(|k| self.own.contains(k));
        }
        let params = self.params();
        let mut calls = Vec::new();
        self.calls(&x[2], &mut calls);
        self.calls(&x[3], &mut calls);
        calls.iter().any(|args| {
            args.len() == params.len() && path.iter().all(|c| params.iter().zip(args.iter()).all(|(p, a)| a == *p || !mentions(c, p)))
        })
    }

    /// The arguments of each application of the definition itself in `x`,
    /// outside binders.
    fn calls<'x>(&self, x: &'x Sx, out: &mut Vec<&'x [Sx]>) {
        let Sx::List(items) = x else { return };
        if is_binder(items) {
            return;
        }
        if matches!(items.first(), Some(Sx::Atom(a)) if a.trim_matches('|') == self.name) {
            out.push(&items[1..]);
        }
        for y in items {
            self.calls(y, out);
        }
    }

    /// A new definition: the parameters and result sort of this one, then
    /// `conds.len()` `Bool`s; its application to the parameters and `conds`.
    fn define(&mut self, body: Sx, conds: Vec<Sx>) -> Sx {
        let n = self.extra.len() + 1;
        let name = Sx::Atom(format!("|{}#if{n}|", self.name));
        let mut args = vec![name.clone()];
        args.extend(self.params().into_iter().cloned());
        let Sx::List(mut all) = self.head[1].clone() else { unreachable!("a head's parameters are a list") };
        for (k, c) in conds.into_iter().enumerate() {
            all.push(Sx::List(vec![Sx::Atom(format!("|if#{k}|")), Sx::Atom("Bool".into())]));
            args.push(c);
        }
        self.extra.push((Sx::List(vec![name, Sx::List(all), self.head[2].clone()]), body));
        Sx::List(args)
    }

    /// `x`, of the definition's result sort, under the split conditions
    /// `path`: an `ite` whose recursive calls Z3 would unfold by propagation
    /// (`stuck`) becomes a definition of its own, split on its condition, and
    /// anything else holding such `ite`s (an application, whose sort may
    /// differ) a definition with a parameter for each of their conditions.
    fn tail(&mut self, x: &Sx, path: &mut Vec<Sx>) -> Sx {
        let Sx::List(items) = x else { return x.clone() };
        if is_binder(items) || matches!(items.first(), Some(Sx::Atom(a)) if a == "let") {
            return x.clone();
        }
        if items.len() == 4 && matches!(&items[0], Sx::Atom(a) if a == "ite") {
            let mut c = Vec::new();
            applies(&items[1], self.index, &mut c);
            let split = c.is_empty();
            let stuck = self.stuck(items, path);
            if split {
                path.push(items[1].clone());
            }
            let (t, e) = (self.tail(&items[2], path), self.tail(&items[3], path));
            if split {
                path.pop();
            }
            if stuck {
                let body = Sx::List(vec![items[0].clone(), Sx::Atom("|if#0|".into()), t, e]);
                return self.define(body, vec![items[1].clone()]);
            }
            return Sx::List(vec![items[0].clone(), items[1].clone(), t, e]);
        }
        let mut conds = Vec::new();
        let body = self.inner(x, path, &mut conds);
        if conds.is_empty() {
            return x.clone();
        }
        self.define(body, conds)
    }

    /// `x` with the condition of each `ite` `stuck` under `path`, outside
    /// binders and conditions, replaced by a parameter, gathered in `conds`.
    fn inner(&mut self, x: &Sx, path: &mut Vec<Sx>, conds: &mut Vec<Sx>) -> Sx {
        let Sx::List(items) = x else { return x.clone() };
        if is_binder(items) || matches!(items.first(), Some(Sx::Atom(a)) if a == "let") {
            return x.clone();
        }
        if items.len() == 4 && matches!(&items[0], Sx::Atom(a) if a == "ite") {
            let mut c = Vec::new();
            applies(&items[1], self.index, &mut c);
            let split = c.is_empty();
            let cond = if self.stuck(items, path) {
                conds.push(items[1].clone());
                Sx::Atom(format!("|if#{}|", conds.len() - 1))
            } else {
                items[1].clone()
            };
            if split {
                path.push(items[1].clone());
            }
            let (t, e) = (self.inner(&items[2], path, conds), self.inner(&items[3], path, conds));
            if split {
                path.pop();
            }
            return Sx::List(vec![items[0].clone(), cond, t, e]);
        }
        Sx::List(items.iter().map(|y| self.inner(y, path, conds)).collect())
    }
}

/// Does `x` mention the atom `a`?
fn mentions(x: &Sx, a: &Sx) -> bool {
    match x {
        Sx::Atom(_) => x == a,
        Sx::List(items) => items.iter().any(|y| mentions(y, a)),
    }
}

pub struct Query {
    pub text: String,
    /// The full query without tables' elements (#638), when it has some.
    pub no_tables: Option<String>,
    /// The same query without the quantified `Nat` axioms: Z3 is complete on
    /// it, so it can find a counterexample where the full query is `unknown`.
    pub without_axioms: Option<String>,
    /// The same query without the postconditions of calls in reflected
    /// bodies (`body_axioms`), when it has some: weaker, so `unsat` still
    /// proves the goal, and most goals need none of them. A model of it may
    /// break them, so `sat` is no counterexample.
    pub without_bodies: Option<String>,
    /// The same query with every reflected definition uninterpreted: weaker,
    /// so `unsat` still proves the goal, and often far faster when the facts
    /// in scope (`have`) already suffice. Tried first.
    pub facts_only: Option<String>,
    /// Only the definitions the goal mentions reflected, without the
    /// quantified axioms: weaker again, and Z3 doesn't unfold functions
    /// whose results the facts in scope already give (M12).
    pub focused: Option<String>,
    /// Only the definitions the facts in scope mention reflected, without
    /// the quantified axioms: the premises unfolded, the goal's functions
    /// not. Z3 unfolds a recursive function without end when the negated
    /// goal rules out its base case's result: each unfolding is forced by
    /// propagation alone, which Z3's limit on unfolding depth doesn't bound,
    /// so it never gets to the case split a premise's body needs.
    pub premised: Option<String>,
    /// Why facts in scope could not be given to the solver.
    pub dropped: Vec<String>,
    /// The obligation's facts left out for a type error (§7.3), by index.
    pub ill_typed: Vec<usize>,
    /// Some facts in scope are `forall`s, not given to the solver (#632):
    /// a model may break them.
    pub foralls: bool,
    /// (SMT name, display name) of the locals, for a counterexample.
    pub shown: Vec<(String, String)>,
    /// The SMT names of `String` locals (shown as text, not bytes).
    pub string_vars: Vec<String>,
    /// Shown variables that are arrays of anything but `U8` (#624).
    pub array_vars: Vec<String>,
}

/// What defining an instance added to a builder, so another builder for the
/// same module can reuse the translation (M12: the definitions are the same
/// for every obligation; translating them was most of a cached check).
#[derive(Clone, Default)]
struct Delta {
    datatypes: Vec<(TyId, usize)>,
    tuples: Vec<usize>,
    sorts: Vec<(String, usize)>,
    funs: Vec<(String, String)>,
    insts: Vec<Inst>,
    known: Vec<(String, Tm)>,
    dict_args: Vec<(String, Vec<Ent>)>,
    axioms: Vec<(String, String)>,
    body_axioms: Vec<(String, String)>,
    asserts: Vec<String>,
    consts: Vec<String>,
    /// The sorts its recognizers are applied at: each query that uses the
    /// translation may need them declared (see `query`).
    tested: Vec<Sort>,
}

/// Translated definitions, shared by the builders of one module.
#[derive(Default)]
pub struct Defs(RefCell<BTreeMap<Inst, (Tx<Defn>, Delta)>>, RefCell<Rewritten>, RefCell<Names>);

/// What the queries of a module would each compute the same way.
#[derive(Default)]
pub struct Names {
    /// Each instance's SMT name.
    names: HashMap<Inst, String>,
    /// Each instance's declaration, uninterpreted.
    uninterp: HashMap<Inst, Option<String>>,
}

/// A table's translation: what it adds to a builder, and its elements' facts.
type Table = (Delta, Vec<String>);

thread_local! {
    /// Tables' translations (#638), for the elaborator they were made with:
    /// the same in every query of every module it checks.
    static TABLES: std::cell::RefCell<(u64, BTreeMap<String, Table>)> = const { std::cell::RefCell::new((0, BTreeMap::new())) };
}

pub struct Builder<'a> {
    e: &'a Elab,
    defs: Option<&'a Defs>,
    user: String,
    datatypes: BTreeMap<TyId, usize>,
    tuples: HashSet<usize>,
    sorts: BTreeMap<String, usize>,
    /// Types with a field whose type can't be a sort (opaque to Z3).
    computed: HashMap<TyId, bool>,
    /// Uninterpreted functions: name → declaration.
    funs: BTreeMap<String, String>,
    /// A local function's type, over the locals before it (#580).
    fun_tys: BTreeMap<String, (usize, Tm)>,
    /// Reflected instances waiting for / with a definition.
    insts: BTreeMap<Inst, Option<Defn>>,
    /// Known function values by key.
    known: BTreeMap<String, Tm>,
    /// Type constructors given to instances, by key (M25).
    ty_funs: BTreeMap<String, Ent>,
    /// A known dictionary over types of the obligation (`Functor (Pair k)`,
    /// M25): its instance's arguments, by its key.
    dict_args: BTreeMap<String, Vec<Ent>>,
    inst_queue: Vec<Inst>,
    consts: Vec<String>,
    asserts: Vec<String>,
    /// Constant tables' elements (#638): only in the full query.
    table_facts: Vec<String>,
    /// `Nat` results of functions, as pattern-guarded axioms (emitted after the definitions).
    axioms: BTreeMap<String, String>,
    /// The postconditions of calls in reflected bodies, as pattern-guarded
    /// axioms (`body_post_axioms`): emitted after `axioms`, and only where
    /// the definitions are reflected.
    body_axioms: BTreeMap<String, String>,
    posts: Vec<PostUse>,
    post_seen: HashSet<String>,
    /// The constant a call with effects being translated is (`effect`).
    effect: Option<String>,
    /// The sort of each call with effects' constant made.
    effect_sorts: HashMap<String, Sort>,
    /// Terms whose type's facts were asserted (once each).
    fact_seen: HashSet<String>,
    /// Each `++` of sequences in the query, by its term: its two operands
    /// (`index_concat`).
    concats: HashMap<String, (String, String)>,
    /// Translating a reflected body: don't collect postconditions or facts
    /// for the query.
    in_def: bool,
    /// Translating the reflected body of `define`: its calls'
    /// postconditions, and the calls they are of (`body_post_axioms`).
    body_posts: Option<(Vec<PostUse>, HashSet<String>)>,
    /// Give the postconditions of calls in reflected bodies (#343): for an
    /// obligation's queries, not for the questions the prover asks itself
    /// (which functions end everywhere, a measure's guess).
    bodies: bool,
    /// The definitions each definition's body names (`reaches`).
    def_refs: HashMap<DefId, Vec<DefId>>,
    /// How many lambdas and `forall`s are being translated.
    lam_depth: usize,
    /// Placeholders for binders whose bodies are being translated (`binders`).
    binder_marks: usize,
    /// Function values given to a local function as fresh constants (`select`).
    fun_args: usize,
    ctx: Vec<Option<Ent>>,
    ctx_src: Vec<ObLocal>,
    /// The type equations' representatives in scope (#209).
    reps: Vec<(Val, Val)>,
    in_assoc_rep: bool,
    /// Classes' types whose base types' sorts are being worked out (#360).
    in_base: Vec<(ConId, usize)>,
    pub shown: Vec<(String, String)>,
    string_vars: Vec<String>,
    array_vars: Vec<String>,
    /// Values the program names, by their datatype: none is a type's
    /// stand-in base constructor (`base_sym`).
    real_values: Vec<(String, TyId)>,
    /// Datatypes given a stand-in base constructor, so Z3 accepts them.
    based: BTreeSet<TyId>,
    /// The sorts a constructor's recognizer is applied at (see `query`).
    tested: BTreeSet<Sort>,
    /// Give `forall` facts to Z3, quantified: only to check a counterexample
    /// against them, never to prove (#632).
    foralls: bool,
    /// Name each fact of the obligation, `|fact.k|` for its `k`th, and ask
    /// for the unsat core: which of them contradict each other.
    named: bool,
}

impl<'a> Builder<'a> {
    pub fn new(e: &'a Elab, user: &str) -> Builder<'a> {
        Builder {
            e,
            defs: None,
            user: user.to_string(),
            datatypes: BTreeMap::new(),
            tuples: HashSet::new(),
            sorts: BTreeMap::new(),
            computed: HashMap::new(),
            funs: BTreeMap::new(),
            fun_tys: BTreeMap::new(),
            insts: BTreeMap::new(),
            known: BTreeMap::new(),
            ty_funs: BTreeMap::new(),
            dict_args: BTreeMap::new(),
            inst_queue: Vec::new(),
            table_facts: Vec::new(),
            consts: Vec::new(),
            asserts: Vec::new(),
            axioms: BTreeMap::new(),
            body_axioms: BTreeMap::new(),
            posts: Vec::new(),
            post_seen: HashSet::new(),
            effect: None,
            effect_sorts: HashMap::new(),
            fun_args: 0,
            fact_seen: HashSet::new(),
            concats: HashMap::new(),
            in_def: false,
            body_posts: None,
            bodies: false,
            def_refs: HashMap::new(),
            lam_depth: 0,
            binder_marks: 0,
            ctx: Vec::new(),
            ctx_src: Vec::new(),
            reps: Vec::new(),
            in_assoc_rep: false,
            in_base: Vec::new(),
            shown: Vec::new(),
            tested: BTreeSet::new(),
            string_vars: Vec::new(),
            array_vars: Vec::new(),
            real_values: Vec::new(),
            based: BTreeSet::new(),
            foralls: false,
            named: false,
        }
    }

    /// Name the obligation's facts and ask Z3 which of them an `unsat`
    /// answer needed (`(get-unsat-core)`, after `(check-sat)`).
    pub fn named_facts(mut self) -> Builder<'a> {
        self.named = true;
        self
    }

    /// Give the `forall` facts in scope to Z3 as quantified formulas, so a
    /// model of the query satisfies them: a counterexample to check one
    /// against (#632 keeps them out of proofs).
    pub fn with_foralls(mut self) -> Builder<'a> {
        self.foralls = true;
        self
    }

    /// Give the postconditions of calls in reflected bodies, where Z3
    /// unfolds the bodies (`body_post_axioms`).
    pub fn with_body_posts(mut self) -> Builder<'a> {
        self.bodies = true;
        self
    }

    /// Share translated definitions with the other builders of the module.
    pub fn sharing(mut self, defs: &'a Defs) -> Builder<'a> {
        self.defs = Some(defs);
        self
    }

    /// `define`, reusing another builder's translation. A translation is
    /// recorded with everything it refers to (sorts, declarations,
    /// instances), translating it in an empty builder, so replaying it is
    /// enough wherever it is used.
    fn define_shared(&mut self, inst: &Inst) -> Tx<Defn> {
        let Some(defs) = self.defs else { return self.define(inst) };
        let found = defs.0.borrow().get(inst).cloned();
        let (r, d) = match found {
            Some(x) => x,
            None => {
                let saved = (
                    std::mem::take(&mut self.datatypes),
                    std::mem::take(&mut self.tuples),
                    std::mem::take(&mut self.sorts),
                    std::mem::take(&mut self.funs),
                    std::mem::take(&mut self.insts),
                    std::mem::take(&mut self.inst_queue),
                    std::mem::take(&mut self.axioms),
                    std::mem::take(&mut self.asserts),
                    std::mem::take(&mut self.consts),
                    std::mem::take(&mut self.tested),
                    std::mem::take(&mut self.body_axioms),
                );
                let known_before: HashSet<String> = self.known.keys().cloned().collect();
                let dict_before: HashSet<String> = self.dict_args.keys().cloned().collect();
                let r = self.define(inst);
                let d = Delta {
                    datatypes: std::mem::replace(&mut self.datatypes, saved.0).into_iter().collect(),
                    tuples: std::mem::replace(&mut self.tuples, saved.1).into_iter().collect(),
                    sorts: std::mem::replace(&mut self.sorts, saved.2).into_iter().collect(),
                    funs: std::mem::replace(&mut self.funs, saved.3).into_iter().collect(),
                    insts: std::mem::replace(&mut self.insts, saved.4).into_keys().collect(),
                    known: self.known.iter().filter(|(k, _)| !known_before.contains(*k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
                    dict_args: self.dict_args.iter().filter(|(k, _)| !dict_before.contains(*k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
                    axioms: std::mem::replace(&mut self.axioms, saved.6).into_iter().collect(),
                    asserts: std::mem::replace(&mut self.asserts, saved.7),
                    consts: std::mem::replace(&mut self.consts, saved.8),
                    tested: std::mem::replace(&mut self.tested, saved.9).into_iter().collect(),
                    body_axioms: std::mem::replace(&mut self.body_axioms, saved.10).into_iter().collect(),
                };
                self.inst_queue = saved.5;
                defs.0.borrow_mut().insert(inst.clone(), (r.clone(), d.clone()));
                (r, d)
            }
        };
        self.datatypes.extend(d.datatypes);
        self.tuples.extend(d.tuples);
        self.sorts.extend(d.sorts);
        for (k, v) in d.funs {
            self.funs.entry(k).or_insert(v);
        }
        for i in d.insts {
            if &i != inst && !self.insts.contains_key(&i) {
                self.insts.insert(i.clone(), None);
                self.inst_queue.push(i);
            }
        }
        for (k, v) in d.known {
            self.known.entry(k).or_insert(v);
        }
        for (k, v) in d.dict_args {
            self.dict_args.entry(k).or_insert(v);
        }
        for (k, v) in d.axioms {
            self.axioms.entry(k).or_insert(v);
        }
        for (k, v) in d.body_axioms {
            self.body_axioms.entry(k).or_insert(v);
        }
        for a in d.asserts {
            if !self.asserts.contains(&a) {
                self.asserts.push(a);
            }
        }
        for c in d.consts {
            if !self.consts.contains(&c) {
                self.consts.push(c);
            }
        }
        self.tested.extend(d.tested);
        r
    }

    fn wk(&self) -> &crate::core::WellKnown {
        &self.e.g.well_known
    }

    // ── sorts ───────────────────────────────────────────────────────────────

    /// Replace solved unknowns (`?m a xs`, as elaboration leaves them) by
    /// their solutions, by evaluating over neutral variables.
    fn zonk(&self, n: usize, t: &Tm) -> Tm {
        if !has_meta(t) {
            return t.clone();
        }
        let env = (0..n).map(Val::var).collect::<crate::core::Env>();
        quote(&self.e.g, n, &eval(&self.e.g, &env, t))
    }

    /// Is this binder's type `Type` (possibly through a solved unknown)?
    fn is_type(&self, t: &Tm) -> bool {
        match t {
            Tm::Univ(_) => true,
            _ if has_meta(t) => {
                let n = max_var(t).map_or(0, |m| m + 1);
                matches!(self.zonk(n, t), Tm::Univ(_))
            }
            _ => false,
        }
    }

    /// Is this binder's type a kind like `Type -> Type` (a type
    /// constructor's, M25)?
    fn is_kind(&self, t: &Tm) -> bool {
        let n = max_var(t).map_or(0, |m| m + 1);
        let mut t = if has_meta(t) { self.zonk(n, t) } else { t.clone() };
        let mut any = false;
        while let Tm::Pi(_, _, _, a, b) = t {
            if !matches!(*a, Tm::Univ(_)) {
                return false;
            }
            any = true;
            t = (*b).clone();
        }
        any && matches!(t, Tm::Univ(_))
    }

    /// A type constructor value, `\y -> T p… y`, as `T` and the sorts of
    /// `p…` (M25).
    fn ty_fun(&mut self, env: &[Ent], t: &Tm) -> Option<Ent> {
        let z = self.zonk(env.len(), t);
        if let Tm::Var(i) = &z {
            return match self.resolve(env, *i).ok()? {
                e @ (Ent::TyFun(..) | Ent::TyVar(_)) => Some(e),
                _ => None,
            };
        }
        // `T p…` unapplied, or eta-expanded.
        let (h, ps) = z.spine_cloned();
        match h {
            Tm::TyCon(id) => {
                let mut pre = Vec::new();
                for p in &ps {
                    pre.push(self.sort_of(env, p).ok()?);
                }
                Some(Ent::TyFun(*id, pre))
            }
            Tm::Lam(_, _, _, body) if ps.is_empty() => match &**body {
                Tm::TyConApp(id, ps) if matches!(ps.last(), Some(Tm::Var(0))) => {
                    let mut inner = env.to_vec();
                    inner.push(Ent::Opaque("a type constructor's own argument".into()));
                    let mut pre = Vec::new();
                    for p in &ps[..ps.len() - 1] {
                        pre.push(self.sort_of(&inner, p).ok()?);
                    }
                    Some(Ent::TyFun(*id, pre))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The sort of a type constructor applied to the sorts of all its
    /// parameters, each of kind `Type` (M25).
    fn ty_sort_sorts(&mut self, id: TyId, sorts: Vec<Sort>) -> Tx<Sort> {
        let e = self.e;
        let wk = &e.g.well_known;
        if Some(id) == wk.array {
            return Ok(Sort::Seq(Box::new(sorts.into_iter().next().ok_or_else(|| Outside("an array without its element type".into()))?)));
        }
        if self.is_bag(id) {
            return Ok(Sort::Bag(Box::new(sorts.into_iter().next().ok_or_else(|| Outside("a bag without its element type".into()))?)));
        }
        let params = self.e.g.tys[id.0 as usize].params.clone();
        if params.len() != sorts.len() || !params.iter().all(|(_, t)| self.is_type(t)) {
            return out("a type constructor with parameters that aren't types");
        }
        let ti = &self.e.g.tys[id.0 as usize];
        if ti.ctors.is_empty() || self.computed_fields(id) {
            let name = format!("{}.{}", ti.module, ti.name);
            self.sorts.insert(name.clone(), sorts.len());
            return Ok(Sort::Unin(name, sorts));
        }
        let sorts = self.with_dict_types(id, sorts);
        if let std::collections::btree_map::Entry::Vacant(e) = self.datatypes.entry(id) {
            e.insert(sorts.len());
            self.datatype_decl(id)?;
        }
        Ok(Sort::Data(id, sorts))
    }

    fn is_bag(&self, t: TyId) -> bool {
        let ti = &self.e.g.tys[t.0 as usize];
        &*ti.module == "std.bag" && &*ti.name == "Bag"
    }

    /// The sort a type term denotes, in `env`.
    fn sort_of(&mut self, env: &[Ent], t: &Tm) -> Tx<Sort> {
        let e = self.e;
        let wk = &e.g.well_known;
        let z = self.zonk(env.len(), t);
        let t = &z;
        // A type equal to another by a type equation in scope (#209): its
        // representative's sort, so both sides have one sort. The equations
        // are about the obligation's locals: an entry of `env` that is one
        // (`@k`) is its level, any other (a callee's parameter, a body's
        // binder) a level past them, which no equation mentions.
        if !self.reps.is_empty() && matches!(t.head(), Tm::Var(_) | Tm::Def(_) | Tm::Field(..)) {
            let n = self.ctx_src.len();
            let vars: Vec<Val> = env
                .iter()
                .enumerate()
                .map(|(k, e)| match e {
                    Ent::Opaque(m) => m.strip_prefix('@').and_then(|l| l.parse().ok()).filter(|l| *l < n).map_or(Val::var(n + k), Val::var),
                    _ => Val::var(n + k),
                })
                .collect();
            let v = eval(&self.e.g, &crate::core::Env::from(vars), t);
            if let Some((_, r)) = self.reps.iter().find(|(m, _)| self.e.same_type_forced(m, &v)).cloned() {
                // The representative is about the obligation's locals too.
                let tm = quote(&self.e.g, n, &r);
                let locals: Vec<Ent> = (0..n).map(|k| Ent::Opaque(format!("@{k}"))).collect();
                let saved = std::mem::take(&mut self.reps);
                let s = self.sort_of(&locals, &tm);
                self.reps = saved;
                return s;
            }
        }
        match t {
            Tm::Var(i) => match self.resolve(env, *i)? {
                Ent::Ty(s) => Ok(s),
                _ => out("a type that depends on a value"),
            },
            Tm::Meta(m) => match self.e.g.meta(*m) {
                Some(v) => {
                    let tm = quote(&self.e.g, env.len(), &v);
                    self.sort_of(env, &tm)
                }
                None => out("a type the checker could not work out"),
            },
            Tm::TupleTy(ts) => {
                let mut ss = Vec::new();
                for t in ts {
                    ss.push(self.sort_of(env, t)?);
                }
                // `(a, (b, c))` is `(a, b, c)` (#673).
                if let Some(Sort::Tuple(ws)) = ss.last().filter(|_| ss.len() >= 2).cloned() {
                    if ws.len() >= 2 {
                        ss.pop();
                        ss.extend(ws);
                    }
                }
                self.tuples.insert(ss.len());
                Ok(Sort::Tuple(ss))
            }
            Tm::TyCon(_) | Tm::TyConApp(..) | Tm::App(..) | Tm::Def(_) => {
                let (h, args) = t.spine_cloned();
                match h {
                    Tm::TyConApp(id, v) => {
                        let mut all = v.clone();
                        all.extend(args);
                        self.ty_sort(env, *id, &all)
                    }
                    Tm::TyCon(id) => self.ty_sort(env, *id, &args),
                    Tm::Var(i) => match self.resolve(env, *i)? {
                        Ent::TyFun(id, pre) => {
                            // `T p…` applied to `a…`: `T p… a…`.
                            let mut all = pre;
                            for a in &args {
                                all.push(self.sort_of(env, a)?);
                            }
                            self.ty_sort_sorts(id, all)
                        }
                        Ent::TyVar(n) => {
                            let mut ss = Vec::new();
                            for a in &args {
                                ss.push(self.sort_of(env, a)?);
                            }
                            self.sorts.insert(n.clone(), ss.len());
                            Ok(Sort::Unin(n, ss))
                        }
                        _ => out("a type that depends on a value"),
                    },
                    // A class's type (#133): at a known instance, its type;
                    // at a dictionary in scope, for a type `t`, a sort of its
                    // own applied to `t`'s (one instance per type).
                    Tm::Def(d) if self.e.g.assoc_def(*d).is_some_and(|(_, _, n)| args.len() == n + 1) => {
                        // Known values (an instance's dictionary) as they are.
                        // A dictionary an instance builds from arguments
                        // (`C (List a)`, #168): the instance's function
                        // applied to variables past `env`, standing for the
                        // arguments kept by its key.
                        let n = env.len();
                        let empty = crate::core::Env::new();
                        let mut extra: Vec<Ent> = Vec::new();
                        let mut venv: Vec<Val> = Vec::with_capacity(n);
                        for (k, e) in env.iter().enumerate() {
                            let v = match e {
                                Ent::Known(key) => match self.known.get(key) {
                                    Some(tm) if crate::core::max_var(tm).is_none() => crate::core::eval(&self.e.g, &empty, tm),
                                    Some(tm) => match (dict_over_vars(tm), self.dict_args.get(key)) {
                                        (Some((f, m)), Some(ents)) if ents.len() == m => {
                                            let base = n + extra.len();
                                            extra.extend(ents.iter().cloned());
                                            let args: Vec<Val> = (0..m).map(|j| Val::var(base + j)).collect();
                                            crate::core::eval(&self.e.g, &crate::core::Env::from(args), &f)
                                        }
                                        _ => Val::var(k),
                                    },
                                    None => Val::var(k),
                                },
                                _ => Val::var(k),
                            };
                            venv.push(v);
                        }
                        let v = crate::core::force(&self.e.g, crate::core::eval(&self.e.g, &crate::core::Env::from(venv), t));
                        match &v {
                            Val::Neutral(crate::core::Head::Var(l), sp) if sp.len() == 1 && *l < n => {
                                let crate::core::Elim::Field(c, i) = sp[0] else { return out("a class's type at a dictionary it can't name") };
                                // The sort of the type the dictionary is for.
                                match self.resolve(env, n - 1 - l)? {
                                    Ent::Term(_, Sort::Data(_, sargs)) if !sargs.is_empty() => Ok(self.dict_field_sort(c, i, &sargs)),
                                    // A dictionary Z3 can't see into (a class
                                    // over a type constructor): named by the
                                    // class's arguments, a type constructor
                                    // by a sort of its own.
                                    Ent::Term(_, Sort::Unin(..)) => {
                                        let cn = args.len() - 1;
                                        let mut ss = Vec::with_capacity(cn);
                                        for a in &args[..cn] {
                                            ss.push(self.class_arg_sort(env, a)?);
                                        }
                                        Ok(self.assoc_sort(c, i, ss))
                                    }
                                    _ => out("a class's type at a dictionary it can't name"),
                                }
                            }
                            // Reduced to a variable: a type parameter, or a
                            // dictionary's argument (`type E = a`).
                            Val::Neutral(crate::core::Head::Var(_), sp) if sp.is_empty() => self.sort_under(env, extra, &v),
                            Val::Neutral(..) => out("a class's type at a dictionary it can't name"),
                            _ => self.sort_under(env, extra, &v),
                        }
                    }
                    Tm::Def(d) => {
                        // A type function applied to closed arguments
                        // (`values (Last Nat)`, #662): the type it gives.
                        let mut fv = std::collections::BTreeSet::new();
                        crate::core::free_vars(t, 0, &mut fv);
                        if fv.is_empty() && !self.e.alias_preds.contains_key(d) {
                            let v = crate::core::eval(&self.e.g, &crate::core::Env::new(), t);
                            if let Some(u) = crate::core::unfold(&self.e.g, &v) {
                                let u = crate::core::force_meta(&self.e.g, u);
                                let stuck = matches!(&u, Val::Neutral(crate::core::Head::Def(d2), _) if d2 == d)
                                    || matches!(&u, Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, crate::core::Elim::Case(..))));
                                if !stuck {
                                    let tm = quote(&self.e.g, env.len(), &u);
                                    return self.sort_of(env, &tm);
                                }
                            }
                        }
                        // A type alias: unfold it.
                        let Some(body) = self.e.g.defs[d.0 as usize].body.clone() else {
                            return out("an abstract type definition");
                        };
                        let mut b = &body;
                        let mut inner: Vec<Ent> = Vec::new();
                        let mut k = 0;
                        while let Tm::Lam(_, _, _, x) = b {
                            let s = match args.get(k) {
                                Some(a) => self.sort_of(env, a).map(Ent::Ty).unwrap_or(Ent::Opaque("arg".into())),
                                None => return out("a partially applied type"),
                            };
                            inner.push(s);
                            b = x;
                            k += 1;
                        }
                        let b = b.clone();
                        self.sort_of(&inner, &b)
                    }
                    _ => out("an unsupported type"),
                }
            }
            _ if wk.nat.is_none() => out("no prelude"),
            Tm::Pi(..) => {
                // A function value (#630): its parameters that aren't erased.
                let mut ps = Vec::new();
                let mut inner = env.to_vec();
                let mut t = t.clone();
                while let Tm::Pi(_, m, _, a, b) = t {
                    if self.is_type(&a) {
                        // An erased type the rest doesn't mention (a class's
                        // parameter passed explicitly to a dictionary's
                        // field, #161) is no parameter of the value.
                        let mut fv = std::collections::BTreeSet::new();
                        crate::core::free_vars(&b, 0, &mut fv);
                        if m != Mult::Zero || fv.contains(&0) {
                            return out("a function of a type (a polymorphic function value)");
                        }
                    }
                    // A parameter's sort names the types read from it (a
                    // class's type at a dictionary parameter).
                    if m != Mult::Zero {
                        let s = self.sort_of(&inner, &a)?;
                        ps.push(s.clone());
                        inner.push(Ent::Term(String::new(), s));
                    } else {
                        inner.push(Ent::Opaque("parameter".into()));
                    }
                    t = (*b).clone();
                }
                if ps.is_empty() {
                    return out("a function without arguments");
                }
                let r = self.sort_of(&inner, &t)?;
                Ok(ps.into_iter().rev().fold(r, |r, p| Sort::Fun(Box::new(p), Box::new(r))))
            }
            Tm::Univ(_) => out("a universe"),
            // A class's type read from a dictionary in scope (`$d.$Unit`, as
            // its functions' fields have it): the sort of `C.Name t`.
            Tm::Field(x, c, i, _) if self.e.g.is_type_field(*c, *i) => match &**x {
                Tm::Var(l) => match self.resolve(env, *l)? {
                    Ent::Term(_, Sort::Data(_, sargs)) if !sargs.is_empty() => Ok(self.dict_field_sort(*c, *i, &sargs)),
                    _ => out("a class's type at a dictionary it can't name"),
                },
                _ => out("a class's type at a dictionary it can't name"),
            },
            _ => out("an unsupported type"),
        }
    }

    /// The sort standing for a class's argument in its types' sorts: a
    /// type's sort, or for a type constructor, a sort of its own.
    fn class_arg_sort(&mut self, env: &[Ent], a: &Tm) -> Tx<Sort> {
        if let Ok(s) = self.sort_of(env, a) {
            return Ok(s);
        }
        let key = match self.ty_fun(env, a) {
            Some(Ent::TyFun(t, ps)) => format!("tyfun#{t:?}{ps:?}"),
            Some(Ent::TyVar(n)) => format!("tyvar#{n}"),
            _ => return out("a class's type at a dictionary it can't name"),
        };
        self.sorts.insert(key.clone(), 0);
        Ok(Sort::Unin(key, Vec::new()))
    }

    /// The sort of a type value under `env` and then `extra` (a
    /// dictionary's arguments, bound past `env`).
    fn sort_under(&mut self, env: &[Ent], extra: Vec<Ent>, v: &Val) -> Tx<Sort> {
        let mut env2 = env.to_vec();
        env2.extend(extra);
        let tm = quote(&self.e.g, env2.len(), v);
        self.sort_of(&env2, &tm)
    }

    /// The sort of a class's type (field `i` of its dictionary's
    /// constructor `c`, #133) at types of sorts `args` (one for each of the
    /// class's parameters, #145): a sort constructor of its own,
    /// `Display.Options a`.
    fn assoc_sort(&mut self, c: ConId, i: usize, args: Vec<Sort>) -> Sort {
        // In its dictionary's datatype declaration, at the sort variables
        // `T0 …`: the datatype's parameter for it (#209).
        let decl = !args.is_empty() && args.iter().enumerate().all(|(k, a)| *a == Sort::Unin(format!("T{k}"), vec![]));
        if decl && i < self.dict_types(c) {
            return Sort::Unin(format!("T{}", args.len() + i), vec![]);
        }
        // A type equation in scope makes it another type (#209).
        if let Some(s) = self.assoc_rep(c, i, &args) {
            return s;
        }
        // A class's type with a base type (#360): its values are the base's.
        if let Some(b) = self.e.g.type_bases.get(&(c, i)).and_then(|bs| bs.first()).cloned().filter(|_| !self.in_base.contains(&(c, i))) {
            self.in_base.push((c, i));
            // Over the class's parameters (of sorts `args`) and a
            // dictionary, whose types are their own sorts.
            let ty = self.e.g.cons[c.0 as usize].ty;
            let mut env: Vec<Ent> = args.iter().map(|a| Ent::Ty(a.clone())).collect();
            let dict = self.with_dict_types(ty, args.clone());
            env.push(Ent::Term(String::new(), Sort::Data(ty, dict)));
            let s = if env.len() == self.e.g.arity_ty(ty) + 1 { self.sort_of(&env, &b).ok() } else { None };
            self.in_base.retain(|k| *k != (c, i));
            if let Some(s) = s {
                return s;
            }
        }
        let ci = &self.e.g.cons[c.0 as usize];
        let ti = &self.e.g.tys[ci.ty.0 as usize];
        let name = format!("{}.{}.{}", ti.module, ti.name, ci.fields[i].0.trim_start_matches('$'));
        self.sorts.insert(name.clone(), args.len());
        Sort::Unin(name, args)
    }

    /// The sort of the representative of a class's type `c`.`i` at
    /// arguments of sorts `args`, if a type equation in scope gives it one.
    fn assoc_rep(&mut self, c: ConId, i: usize, args: &[Sort]) -> Option<Sort> {
        if self.reps.is_empty() || self.in_assoc_rep {
            return None;
        }
        self.in_assoc_rep = true;
        let mut found = None;
        for (m, r) in self.reps.clone() {
            let Val::Neutral(crate::core::Head::Var(l), sp) = force(&self.e.g, m.clone()) else { continue };
            if sp.len() != 1 || !matches!(sp[0], crate::core::Elim::Field(c2, i2) if c2 == c && i2 == i) || l >= self.ctx_src.len() {
                continue;
            }
            // The dictionary's class's arguments' sorts, as written for it.
            let Val::TyCon(_, targs) = force(&self.e.g, self.ctx_src[l].ty.clone()) else { continue };
            let env: Vec<Ent> = (0..l).map(|k| Ent::Opaque(format!("@{k}"))).collect();
            let mut ps = Vec::new();
            for a in targs.iter() {
                let tm = quote(&self.e.g, l, a);
                if self.is_type(&tm) || matches!(force(&self.e.g, a.clone()), Val::Neutral(..) | Val::TyCon(..) | Val::TupleTy(_)) {
                    if let Ok(s) = self.sort_of(&env, &tm) {
                        ps.push(s);
                    }
                }
            }
            if ps == args {
                let n = self.ctx_src.len();
                let tm = quote(&self.e.g, n, &r);
                let env: Vec<Ent> = (0..n).map(|k| Ent::Opaque(format!("@{k}"))).collect();
                found = self.sort_of(&env, &tm).ok();
                break;
            }
        }
        self.in_assoc_rep = false;
        found
    }

    /// A type-valued field's sort, in a datatype's declaration: a class's
    /// type at the class's parameter (#133), or a sort of its own.
    fn type_field_sort(&mut self, c: ConId, i: usize, env: &[Ent]) -> Sort {
        let f = &self.e.g.cons[c.0 as usize].fields[i];
        if f.0.starts_with('$') {
            let n = self.e.g.arity_ty(self.e.g.cons[c.0 as usize].ty);
            let ps: Vec<Sort> = env.iter().take(n).filter_map(|e| if let Ent::Ty(p) = e { Some(p.clone()) } else { None }).collect();
            if n > 0 && ps.len() == n {
                return self.assoc_sort(c, i, ps);
            }
        }
        self.sorts.insert("field".into(), 0);
        Sort::Unin("field".into(), vec![])
    }

    fn ty_sort(&mut self, env: &[Ent], id: TyId, args: &[Tm]) -> Tx<Sort> {
        let e = self.e;
        let wk = &e.g.well_known;
        if Some(id) == wk.int {
            return Ok(Sort::Int);
        }
        if Some(id) == wk.bool_ty {
            return Ok(Sort::Bool);
        }
        if Some(id) == wk.string {
            return Ok(Sort::Str);
        }
        if Some(id) == wk.array {
            let a = args.first().ok_or_else(|| Outside("an array without its element type".into()))?;
            return Ok(Sort::Seq(Box::new(self.sort_of(env, a)?)));
        }
        if self.is_bag(id) {
            let a = args.first().ok_or_else(|| Outside("a bag without its element type".into()))?;
            return Ok(Sort::Bag(Box::new(self.sort_of(env, a)?)));
        }
        // Only type parameters (of kind `Type`) become sort parameters.
        let params = self.e.g.tys[id.0 as usize].params.clone();
        let mut sargs = Vec::new();
        for (k, (_, pty)) in params.iter().enumerate() {
            if self.is_type(pty) {
                let a = args.get(k).ok_or_else(|| Outside("a partially applied type".into()))?;
                sargs.push(self.sort_of(env, a)?);
            }
        }
        let ti = &self.e.g.tys[id.0 as usize];
        // A type without constructors, or one with a field whose type is
        // computed from its parameters (`Spawned ss`, #611), is opaque to Z3:
        // it knows nothing about its values, which can only prove less.
        if ti.ctors.is_empty() || self.computed_fields(id) {
            let name = format!("{}.{}", ti.module, ti.name);
            self.sorts.insert(name.clone(), sargs.len());
            return Ok(Sort::Unin(name, sargs));
        }
        let sargs = self.with_dict_types(id, sargs);
        let n = sargs.len();
        if let std::collections::btree_map::Entry::Vacant(e) = self.datatypes.entry(id) {
            e.insert(n);
            // Register the field types' datatypes too.
            self.datatype_decl(id)?;
        }
        Ok(Sort::Data(id, sargs))
    }

    /// A class's dictionary's datatype takes its class's types' sorts as
    /// parameters after its type parameters' (#209): `(Seq s E)`, where `E`
    /// is `Seq.Elem s`'s sort, so where a type equation makes `Seq.Elem s`
    /// a `U8` its functions' fields have `Int` elements.
    fn with_dict_types(&mut self, id: TyId, mut sargs: Vec<Sort>) -> Vec<Sort> {
        let Some(&c) = self.e.g.tys[id.0 as usize].ctors.first() else { return sargs };
        let m = self.dict_types(c);
        let ps = sargs.clone();
        for i in 0..m {
            let s = self.assoc_sort(c, i, ps.clone());
            sargs.push(s);
        }
        sargs
    }

    /// How many of a class's types its dictionary's constructor `c` keeps
    /// (its first fields); 0 for any other constructor.
    fn dict_types(&self, c: ConId) -> usize {
        let n = self.e.g.cons[c.0 as usize].fields.len();
        (0..n).take_while(|&k| self.e.g.is_dict_type_field(c, k)).count()
    }

    /// How many type parameters the class of dictionary constructor `c`
    /// has: its dictionary's sort's first arguments (its types' follow).
    fn class_params(&self, c: ConId) -> usize {
        let ty = self.e.g.cons[c.0 as usize].ty;
        self.e.g.tys[ty.0 as usize].params.iter().filter(|(_, t)| self.is_type(t)).count()
    }

    /// The sort of a class's type, field `i` of a dictionary of sort
    /// `Data(_, sargs)`: its parameter there.
    fn dict_field_sort(&mut self, c: ConId, i: usize, sargs: &[Sort]) -> Sort {
        let ty = self.e.g.cons[c.0 as usize].ty;
        let n = self.e.g.tys[ty.0 as usize].params.iter().filter(|(_, t)| self.is_type(t)).count();
        match sargs.get(n + i) {
            Some(s) if self.dict_types(c) > i => s.clone(),
            _ => self.assoc_sort(c, i, sargs[..n.min(sargs.len())].to_vec()),
        }
    }

    /// Does a constructor of `id` have a field whose type can't be a sort?
    fn computed_fields(&mut self, id: TyId) -> bool {
        if let Some(r) = self.computed.get(&id) {
            return *r;
        }
        // Assume not while looking, for recursive types.
        self.computed.insert(id, false);
        let env = self.decl_env(id);
        let saved = (self.sorts.clone(), self.datatypes.clone(), self.tuples.clone());
        let mut r = false;
        for c in self.e.g.tys[id.0 as usize].ctors.clone() {
            let fields = self.e.g.cons[c.0 as usize].fields.clone();
            let mut env = env.clone();
            for (k, f) in fields.iter().enumerate() {
                if self.is_type(&f.3) {
                    let s = self.type_field_sort(c, k, &env);
                    env.push(Ent::Ty(s));
                    continue;
                }
                match self.sort_of(&env, &f.3) {
                    Ok(s) => env.push(Ent::Term(String::new(), s)),
                    Err(_) => {
                        r = true;
                        break;
                    }
                }
            }
        }
        // Looking may have registered sorts; keep only what the query needs.
        (self.sorts, self.datatypes, self.tuples) = saved;
        self.computed.insert(id, r);
        r
    }

    /// The parameter environment of a datatype declaration: type parameters
    /// are the sort variables `T0, T1, …`; value parameters are opaque.
    fn decl_env(&self, id: TyId) -> Vec<Ent> {
        let params = &self.e.g.tys[id.0 as usize].params;
        let mut k = 0;
        params
            .iter()
            .map(|(_, t)| {
                if self.is_type(t) {
                    k += 1;
                    Ent::Ty(Sort::Unin(format!("T{}", k - 1), vec![]))
                } else {
                    Ent::Opaque("value parameter".into())
                }
            })
            .collect()
    }

    /// The SMT fields of a constructor: (field index, sort), skipping type-valued fields.
    fn con_fields(&mut self, c: ConId, env: &[Ent]) -> Tx<Vec<(usize, Sort)>> {
        let fields = self.e.g.cons[c.0 as usize].fields.clone();
        let mut env = env.to_vec();
        let mut out_ = Vec::new();
        for (k, f) in fields.iter().enumerate() {
            match &f.3 {
                ty if self.is_type(ty) => {
                    let s = self.type_field_sort(c, k, &env);
                    env.push(Ent::Ty(s));
                }
                ty => {
                    let s = self.sort_of(&env, ty)?;
                    out_.push((k, s.clone()));
                    env.push(Ent::Term(String::new(), s));
                }
            }
        }
        Ok(out_)
    }

    fn datatype_decl(&mut self, id: TyId) -> Tx<()> {
        let env = self.decl_env(id);
        for c in self.e.g.tys[id.0 as usize].ctors.clone() {
            self.con_fields(c, &env)?;
        }
        Ok(())
    }

    fn sort_decls(&mut self) -> Tx<Vec<String>> {
        let mut out_ = Vec::new();
        for (name, n) in &self.sorts {
            out_.push(format!("(declare-sort {} {n})", sym(name)));
        }
        // Each declaration: (head, body, the heads its fields mention).
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum Head {
            Tuple(usize),
            Data(TyId),
        }
        fn mentions(s: &Sort, out_: &mut BTreeSet<Head>) {
            match s {
                Sort::Data(t, args) => {
                    out_.insert(Head::Data(*t));
                    args.iter().for_each(|a| mentions(a, out_));
                }
                Sort::Tuple(xs) => {
                    out_.insert(Head::Tuple(xs.len()));
                    xs.iter().for_each(|a| mentions(a, out_));
                }
                Sort::Unin(_, xs) => xs.iter().for_each(|a| mentions(a, out_)),
                Sort::Fun(p, r) => {
                    mentions(p, out_);
                    mentions(r, out_);
                }
                Sort::Seq(x) | Sort::Bag(x) => mentions(x, out_),
                _ => {}
            }
        }
        // Each datatype's constructors' field sorts, to find those Z3 would
        // reject as not well-founded (`base_sym`).
        let mut fields_of: BTreeMap<TyId, Vec<Vec<Sort>>> = BTreeMap::new();
        let mut decls: BTreeMap<Head, (String, String, BTreeSet<Head>)> = BTreeMap::new();
        for &n in &self.tuples {
            let ps: Vec<String> = (0..n).map(|k| format!("T{k}")).collect();
            let fields: Vec<String> = (0..n).map(|k| format!("({} T{k})", tuple_sel(n, k))).collect();
            let ctor = format!("({} {})", tuple_con(n), fields.join(" "));
            let body = if n == 0 { format!("(({}))", tuple_con(0)) } else { format!("(par ({}) ({ctor}))", ps.join(" ")) };
            decls.insert(Head::Tuple(n), (format!("({} {n})", tuple_sym(n)), body, BTreeSet::new()));
        }
        let ids: Vec<(TyId, usize)> = self.datatypes.iter().map(|(a, b)| (*a, *b)).collect();
        for (id, n) in ids {
            let env = self.decl_env(id);
            let mut ctors = Vec::new();
            let mut deps = BTreeSet::new();
            let mut sorts = Vec::new();
            for c in self.e.g.tys[id.0 as usize].ctors.clone() {
                let fs = self.con_fields(c, &env)?;
                fs.iter().for_each(|(_, s)| mentions(s, &mut deps));
                sorts.push(fs.iter().map(|(_, s)| s.clone()).collect());
                let fields: Vec<String> =
                    fs.iter().map(|(k, s)| format!("({} {})", sel_sym(self.e, c, *k), s.render(self.e))).collect();
                ctors.push(if fields.is_empty() {
                    format!("({})", con_sym(self.e, c))
                } else {
                    format!("({} {})", con_sym(self.e, c), fields.join(" "))
                });
            }
            fields_of.insert(id, sorts);
            // The body without its closing parentheses: a stand-in
            // constructor may be added. Its fields name its parameters as
            // sorts (`Sort::Unin`), so they are spelled as `sym` does.
            let ps: Vec<String> = (0..n).map(|k| sym(&format!("T{k}"))).collect();
            let body = if n == 0 {
                format!("({}", ctors.join(" "))
            } else {
                format!("(par ({}) ({}", ps.join(" "), ctors.join(" "))
            };
            decls.insert(Head::Data(id), (format!("({} {n})", ty_sym(self.e, id)), body, deps));
        }
        // Does a sort have a value Z3 can see without the group's datatypes
        // whose bases aren't known yet? Z3 takes a datatype declared earlier
        // as having values, and doesn't look through an array (`Seq`, `Bag`,
        // a function) for one.
        fn based(s: &Sort, group: &[Head], known: &BTreeSet<Head>) -> bool {
            let mut m = BTreeSet::new();
            match s {
                Sort::Data(t, _) if group.contains(&Head::Data(*t)) => known.contains(&Head::Data(*t)),
                Sort::Tuple(xs) => xs.iter().all(|x| based(x, group, known)),
                Sort::Seq(_) | Sort::Bag(_) | Sort::Fun(..) => {
                    mentions(s, &mut m);
                    !m.iter().any(|h| group.contains(h))
                }
                _ => true,
            }
        }
        // Z3 rejects a group whose members use a sibling at other parameters
        // (`List (Tuple2 String Json)` beside `Json`), so declare each strongly
        // connected group on its own, dependencies first.
        let keys: Vec<Head> = decls.keys().copied().collect();
        let reach = |from: Head| -> BTreeSet<Head> {
            let mut seen = BTreeSet::new();
            let mut stack = vec![from];
            while let Some(h) = stack.pop() {
                for d in decls.get(&h).map(|x| x.2.clone()).unwrap_or_default() {
                    if decls.contains_key(&d) && seen.insert(d) {
                        stack.push(d);
                    }
                }
            }
            seen
        };
        let reaches: BTreeMap<Head, BTreeSet<Head>> = keys.iter().map(|&k| (k, reach(k))).collect();
        let mut done: BTreeSet<Head> = BTreeSet::new();
        while done.len() < keys.len() {
            // A group whose dependencies outside itself are all declared.
            let mut progressed = false;
            for &k in &keys {
                if done.contains(&k) {
                    continue;
                }
                let group: Vec<Head> = keys
                    .iter()
                    .copied()
                    .filter(|&j| j == k || (reaches[&k].contains(&j) && reaches[&j].contains(&k)))
                    .collect();
                let ready = reaches[&k].iter().all(|d| done.contains(d) || group.contains(d));
                if !ready {
                    continue;
                }
                let mut known: BTreeSet<Head> = group.iter().copied().filter(|h| matches!(h, Head::Tuple(_))).collect();
                loop {
                    let more: Vec<Head> = group
                        .iter()
                        .copied()
                        .filter(|h| !known.contains(h))
                        .filter(|h| {
                            let Head::Data(id) = h else { return false };
                            fields_of[id].iter().any(|fs| fs.iter().all(|s| based(s, &group, &known)))
                        })
                        .collect();
                    if more.is_empty() {
                        break;
                    }
                    known.extend(more);
                }
                let heads: Vec<&str> = group.iter().map(|h| decls[h].0.as_str()).collect();
                let mut bodies = Vec::new();
                for h in &group {
                    let body = &decls[h].1;
                    bodies.push(match h {
                        Head::Tuple(_) => body.clone(),
                        Head::Data(id) => {
                            let n = self.datatypes[id];
                            let close = if n == 0 { ")" } else { "))" };
                            if known.contains(h) {
                                format!("{body}{close}")
                            } else {
                                self.based.insert(*id);
                                format!("{body} ({}){close}", base_sym(self.e, *id))
                            }
                        }
                    });
                }
                out_.push(format!("(declare-datatypes ({}) ({}))", heads.join(" "), bodies.join(" ")));
                done.extend(group);
                progressed = true;
            }
            if !progressed {
                return out("cyclic datatype declarations");
            }
        }
        Ok(out_)
    }

    // ── terms ───────────────────────────────────────────────────────────────

    fn local(&mut self, lvl: usize) -> Tx<Ent> {
        if let Some(Some(e)) = self.ctx.get(lvl) {
            return Ok(e.clone());
        }
        // A program local's facts hold everywhere, wherever it is first met
        // (a reflected body, a quantified axiom's guard).
        let saved = std::mem::replace(&mut self.in_def, false);
        let r = self.declare_local(lvl);
        self.in_def = saved;
        r
    }

    /// `local`'s work: declare the local `lvl`, with its facts.
    fn declare_local(&mut self, lvl: usize) -> Tx<Ent> {
        let l = self.ctx_src[lvl].clone();
        let env: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let ty = force(&self.e.g, l.ty.clone());
        let name = sym(&format!("{}#{lvl}", l.name));
        let ent = match &ty {
            Val::Univ(_) => {
                let s = format!("{}#{lvl}", l.name);
                self.sorts.insert(s.clone(), 0);
                Ent::Ty(Sort::Unin(s, vec![]))
            }
            Val::Pi(..) if self.is_kind(&quote(&self.e.g, lvl, &ty)) => {
                // A type constructor variable (M25).
                Ent::TyVar(format!("{}#{lvl}", l.name))
            }
            Val::Pi(..) => {
                // A local function: a function value (#630), so it can be
                // passed on as it is.
                let tyt = quote(&self.e.g, lvl, &ty);
                let s = self.sort_of(&env, &tyt)?;
                self.consts.push(format!("(declare-const {name} {})", s.render(self.e)));
                // Declared, so known from here on: its specification is over
                // all the locals, and may mention it (a precondition's
                // dictionary is applied to every local in scope, #210).
                self.ctx[lvl] = Some(Ent::Term(name.clone(), s.clone()));
                // Its refinements may mention later locals (#102): its
                // specification is over all of them.
                let (at, spec) = match &l.refined {
                    Some(r) => (self.ctx_src.len(), quote(&self.e.g, self.ctx_src.len(), r)),
                    None => (lvl, tyt),
                };
                self.fun_tys.insert(name.clone(), (at, spec));
                self.fun_axiom(&name, at);
                Ent::Term(name.clone(), s)
            }
            _ => {
                let tyt = quote(&self.e.g, lvl, &ty);
                let s = self.sort_of(&env, &tyt)?;
                self.consts.push(format!("(declare-const {name} {})", s.render(self.e)));
                let nat = self.is_nat_val(&l.ty).then(|| format!("(>= {name} 0)"));
                self.asserts.extend(nat.clone());
                // What its type says beyond the sort: a refinement alias's
                // predicates (`U8`), its parts' and fields' (`(Char,
                // (stop~Nat, k < stop))`, `Parsed Members …`), its
                // constructor's invariants (#505).
                let raw = quote(&self.e.g, lvl, &l.ty);
                let facts = self.value_terms(&env, &raw, &name, &s);
                self.asserts.extend(facts.into_iter().filter(|t| Some(t) != nat.as_ref()));
                if s == Sort::Str {
                    self.string_fact(&name);
                }
                if let Sort::Data(id, _) = &s {
                    self.real_values.push((name.clone(), *id));
                }
                if !l.name.starts_with('$') && !l.name.starts_with('_') {
                    self.shown.push((name.clone(), l.name.to_string()));
                    if s == Sort::Str {
                        self.string_vars.push(name.clone());
                    }
                    if let Val::TyCon(id, args) = crate::core::force(&self.e.g, l.ty.clone()) {
                        let byte = checkers_rt::array::Layout::U8 as u8;
                        if Some(id) == self.e.g.well_known.array
                            && args.first().is_none_or(|a| crate::core::layout_of(&self.e.g, a) != Ok(byte))
                        {
                            self.array_vars.push(name.clone());
                        }
                    }
                }
                Ent::Term(name.clone(), s)
            }
        };
        self.ctx[lvl] = Some(ent.clone());
        // A `let`-bound local equals its value.
        if let (Some(def), Ent::Term(n, s)) = (&l.def, &ent) {
            let tm = quote(&self.e.g, lvl, def);
            if let Ok((v, vs)) = self.term_ctx(lvl, &tm) {
                // Not a value with a type error (§7.3).
                if self.expect(&vs, s).is_ok() {
                    self.asserts.push(format!("(= {n} {v})"));
                }
            }
        }
        Ok(ent)
    }

    /// The prelude's `valid_utf8`, applied to `t` (bytes): its term.
    fn valid_utf8(&mut self, t: &str) -> Option<String> {
        let g = &self.e.g;
        let d = g.defs.iter().position(|d| &*d.module == "std.prelude" && &*d.name == "valid_utf8")?;
        let env = vec![Ent::Term(t.to_string(), Sort::Seq(Box::new(Sort::Int)))];
        let tm = Tm::App(Rc::new(Tm::Def(DefId(d as u32))), Rc::new(Tm::Var(0)), crate::core::Icit::Expl, Mult::Many, crate::core::Pos::NONE);
        match self.term(&env, &tm) {
            Ok((ft, Sort::Bool)) => Some(ft),
            _ => None,
        }
    }

    /// A string's bytes are UTF-8 (#170): what `String`'s field says.
    fn string_fact(&mut self, t: &str) {
        if let Some(f) = self.valid_utf8(t) {
            self.asserts.push(f);
        }
    }

    /// Whether the bytes of a literal are UTF-8, which `valid_utf8` says of
    /// it: the prover knows nothing else of that builtin (#170).
    fn literal_utf8(&mut self, b: &[u8]) {
        let lit = smt_bytes(b);
        if self.in_def || !self.fact_seen.insert(format!("utf8 {lit}")) {
            return;
        }
        if let Some(f) = self.valid_utf8(&lit) {
            self.asserts.push(if std::str::from_utf8(b).is_ok() { f } else { format!("(not {f})") });
        }
    }

    /// A call `f a…` of a local function whose type is refined (#580): where
    /// its preconditions hold at the arguments, its postconditions hold at
    /// the result.
    /// `ats` are the explicit arguments' terms and sorts, as the call has them.
    fn fun_post_facts(&mut self, args: &[(Tm, Mult)], ats: &[(String, Sort)], name: &str, app: &str, rs: &Sort) {
        let Some((lvl, ty)) = self.fun_tys.get(name).cloned() else { return };
        let mut inner: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let mut pres = Vec::new();
        let mut t = ty;
        let mut ats = ats.iter();
        for (_, m) in args {
            let Tm::Pi(_, _, _, dom, cod) = t else { return };
            if *m == Mult::Zero {
                inner.push(Ent::Opaque("type argument".into()));
            } else {
                let Some((at, s)) = ats.next().cloned() else { return };
                pres.extend(self.domain_terms(&inner, &dom, &at, &s));
                inner.push(Ent::Term(at, s));
            }
            t = (*cod).clone();
        }
        let posts = self.value_terms(&inner, &t, app, rs);
        if posts.is_empty() {
            return;
        }
        let post = if posts.len() == 1 { posts[0].clone() } else { format!("(and {})", posts.join(" ")) };
        self.asserts.push(match pres.len() {
            0 => post,
            1 => format!("(=> {} {post})", pres[0]),
            _ => format!("(=> (and {}) {post})", pres.join(" ")),
        });
    }

    /// A local function of a refined type (#580) is so at every argument, not
    /// only at the calls written: where its preconditions hold, its
    /// postconditions hold, for each application Z3 makes (unfolding `map f`,
    /// #630). A pattern-guarded axiom, like `nat_axiom`'s.
    fn fun_axiom(&mut self, name: &str, lvl: usize) {
        // Its terms are over the axiom's bound variables: facts about them
        // (`Seq.size x0` is a `Nat`) can't be stated outside it (#210).
        let saved = std::mem::replace(&mut self.in_def, true);
        self.fun_axiom_in(name, lvl);
        self.in_def = saved;
    }

    fn fun_axiom_in(&mut self, name: &str, lvl: usize) {
        let Some((_, ty)) = self.fun_tys.get(name).cloned() else { return };
        let mut inner: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let mut pres = Vec::new();
        let mut vars = Vec::new();
        let mut t = ty;
        while let Tm::Pi(_, m, _, dom, cod) = t {
            if m == Mult::Zero {
                inner.push(Ent::Opaque("type argument".into()));
            } else {
                let Ok(s) = self.sort_of(&inner, &dom) else { return };
                let v = format!("x{}", vars.len());
                pres.extend(self.domain_terms(&inner, &dom, &v, &s));
                vars.push((v.clone(), s.clone()));
                inner.push(Ent::Term(v, s));
            }
            t = (*cod).clone();
        }
        let Ok(rs) = self.sort_of(&inner, &t) else { return };
        let mut app = name.to_string();
        for (v, _) in &vars {
            app = format!("(select {app} {v})");
        }
        let posts = self.value_terms(&inner, &t, &app, &rs);
        if posts.is_empty() || vars.is_empty() {
            return;
        }
        let conj = |xs: &[String]| if xs.len() == 1 { xs[0].clone() } else { format!("(and {})", xs.join(" ")) };
        let body = if pres.is_empty() { conj(&posts) } else { format!("(=> {} {})", conj(&pres), conj(&posts)) };
        let binds: Vec<String> = vars.iter().map(|(v, s)| format!("({v} {})", s.render(self.e))).collect();
        // After the function's own declaration, so among the facts.
        self.asserts.push(format!("(forall ({}) (! {body} :pattern ({app})))", binds.join(" ")));
    }

    /// What a value `x` of type `ty` (sort `xs`) satisfies beyond its sort
    /// (#554, #576): a `Nat` is non-negative, a refinement alias's predicates
    /// hold, and so do those of its parts and fields, nested: a tuple's
    /// parts, and a datatype's fields at their declared types, with the
    /// type's arguments put in (`Pair Nat (j~Nat, i <= j)`, `Parsed Members
    /// …`), each constructor's under its tester, with its invariants (#505).
    /// As facts to assume of a value the program has.
    fn value_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) -> Vec<String> {
        self.type_terms(env, ty, x, xs, Some(&mut Vec::new()), true)
    }

    /// `value_terms` of `x`'s parts and fields only, not of `x` itself: a
    /// call's result, whose own refinement its postconditions give.
    fn part_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) -> Vec<String> {
        self.type_terms(env, ty, x, xs, Some(&mut Vec::new()), false)
    }

    /// `value_terms` without looking inside datatypes: what a value must
    /// satisfy to be in the type, as a guard (a `forall`'s variables, a
    /// function value's arguments), where Z3 must show it of the values it
    /// picks.
    fn domain_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) -> Vec<String> {
        self.type_terms(env, ty, x, xs, None, true)
    }

    /// `value_terms`, and `domain_terms` without `inside`. `inside` holds the
    /// datatypes being looked into: a field of one of them again (a list's
    /// tail, of the same type as the list) is not, so the facts stay finite,
    /// and nor is one `DATA_DEPTH` datatypes deep (a value deeper has its
    /// facts where the program names it, by a pattern or a field). Without
    /// `top`, only what is said of the parts.
    fn type_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort, inside: Option<&mut Vec<String>>, top: bool) -> Vec<String> {
        let mut out = Vec::new();
        // A function's refinements are its own (`fun_axiom`, #630).
        if matches!(xs, Sort::Fun(..)) {
            return out;
        }
        let ty = if has_meta(ty) { self.zonk(env.len(), ty) } else { ty.clone() };
        // A class's type at a known instance is the instance's, refinements
        // and all (#190).
        let ty = match ty.head() {
            Tm::Def(_) => {
                let n = env.len();
                let vars = (0..n).map(Val::var).collect::<crate::core::Env>();
                match crate::core::class_type_at(&self.e.g, &eval(&self.e.g, &vars, &ty)) {
                    Some(v) => quote(&self.e.g, n, &v),
                    None => ty,
                }
            }
            _ => ty,
        };
        // `Nat` is also the alias `n~Int, n >= 0`: each term once.
        let add = |out: &mut Vec<String>, ts: Vec<String>| {
            for t in ts {
                if !out.contains(&t) {
                    out.push(t);
                }
            }
        };
        // A class's type at a dictionary in scope: its declared predicates
        // hold of every value of it (#176), a call's result too.
        let ts = self.class_type_terms(env, &ty, x, xs);
        add(&mut out, ts);
        if top {
            if self.is_nat_tm(&ty) {
                out.push(format!("(>= {x} 0)"));
            }
            let ts = self.alias_terms(env, &ty, x, xs);
            add(&mut out, ts);
        }
        // Its shape: through the aliases it is written with.
        let shape = match ty.head() {
            Tm::Def(_) => {
                let n = env.len();
                let vars = (0..n).map(Val::var).collect::<crate::core::Env>();
                quote(&self.e.g, n, &force(&self.e.g, eval(&self.e.g, &vars, &ty)))
            }
            _ => ty,
        };
        match (&shape, xs) {
            (Tm::TupleTy(ts), Sort::Tuple(ss)) => {
                let mut inside = inside;
                let n = ss.len();
                for (k, t) in ts.iter().enumerate() {
                    // A last part that is a tuple is flattened (#673): the
                    // last of `ts` is the tuple of the remaining components.
                    let (part, ps) = if k + 1 == ts.len() && ts.len() < n {
                        let rest = Sort::Tuple(ss[k..].to_vec());
                        self.tuples.insert(n - k);
                        let parts: Vec<String> = (k..n).map(|j| format!("({} {x})", tuple_sel(n, j))).collect();
                        (format!("((as {} {}) {})", tuple_con(n - k), rest.render(self.e), parts.join(" ")), rest)
                    } else {
                        let Some(p) = ss.get(k) else { break };
                        (format!("({} {x})", tuple_sel(n, k)), p.clone())
                    };
                    let ts = self.type_terms(env, t, &part, &ps, inside.as_deref_mut(), true);
                    add(&mut out, ts);
                }
            }
            (_, Sort::Data(id, sargs)) => {
                if let Some(inside) = inside {
                    // The type, the same at any depth of locals.
                    let n = env.len();
                    let vars = (0..n).map(Val::var).collect::<crate::core::Env>();
                    let key = format!("{:?}", quote(&self.e.g, 1 << 20, &eval(&self.e.g, &vars, &shape)));
                    if !inside.contains(&key) && inside.len() < DATA_DEPTH {
                        inside.push(key);
                        let ts = self.field_terms(env, &shape, x, *id, sargs, inside);
                        inside.pop();
                        add(&mut out, ts);
                    }
                }
            }
            _ => {}
        }
        out
    }

    /// The fields of `x`, of datatype `ty` (`id` at sorts `sargs`): for each
    /// constructor, what its fields' types say of them and its invariants,
    /// under its tester unless it is the only one. A field's type is the
    /// declared one with `ty`'s arguments (types and values) and the fields
    /// before it put in, by evaluation, so nothing is captured.
    fn field_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, id: TyId, sargs: &[Sort], inside: &mut Vec<String>) -> Vec<String> {
        let (h, mut args) = ty.spine_cloned();
        match h {
            Tm::TyConApp(i, v) if *i == id => {
                let mut all = v.clone();
                all.extend(args);
                args = all;
            }
            Tm::TyCon(i) if *i == id => {}
            _ => return Vec::new(),
        }
        if args.len() != self.e.g.tys[id.0 as usize].params.len() {
            return Vec::new();
        }
        let n = env.len();
        let vars = (0..n).map(Val::var).collect::<crate::core::Env>();
        let params: Vec<Val> = args.iter().map(|a| eval(&self.e.g, &vars, a)).collect();
        let senv = self.sort_env(id, sargs);
        let ctors = self.e.g.tys[id.0 as usize].ctors.clone();
        let mut out = Vec::new();
        for &c in &ctors {
            let Ok(fs) = self.con_fields(c, &senv) else { continue };
            let fields = self.e.g.cons[c.0 as usize].fields.clone();
            let mut ext = env.to_vec();
            let mut vals = params.clone();
            let mut facts: Vec<String> = Vec::new();
            for (k, f) in fields.iter().enumerate() {
                match fs.iter().find(|(i, _)| *i == k) {
                    Some((_, fsort)) => {
                        let sel = format!("({} {x})", sel_sym(self.e, c, k));
                        let fty = quote(&self.e.g, n + k, &eval(&self.e.g, &crate::core::Env::from(vals.clone()), &f.3));
                        for t in self.type_terms(&ext, &fty, &sel, fsort, Some(inside), true) {
                            if !facts.contains(&t) {
                                facts.push(t);
                            }
                        }
                        ext.push(Ent::Term(sel, fsort.clone()));
                    }
                    None => {
                        let s = self.type_field_sort(c, k, &senv);
                        ext.push(Ent::Ty(s));
                    }
                }
                vals.push(Val::var(n + k));
            }
            // Invariants may mention the type's value parameters
            // (`stop <= len src`).
            let vals = crate::core::Env::from(vals);
            for inv in self.e.con_invs.get(&c).cloned().unwrap_or_default() {
                let tm = quote(&self.e.g, n + fields.len(), &eval(&self.e.g, &vals, &inv.tm));
                let saved = self.in_def;
                self.in_def = true;
                if let Ok((t, Sort::Bool)) = self.term(&ext, &tm) {
                    if !facts.contains(&t) {
                        facts.push(t);
                    }
                }
                self.in_def = saved;
            }
            if facts.is_empty() {
                continue;
            }
            let all = if facts.len() == 1 { facts.pop().unwrap() } else { format!("(and {})", facts.join(" ")) };
            if ctors.len() != 1 {
                self.tested.insert(Sort::Data(id, sargs.to_vec()));
            }
            out.push(if ctors.len() == 1 { all } else { format!("(=> ({} {x}) {all})", tester(self.e, c)) });
        }
        out
    }

    /// The type `ty`'s result at the arguments `args` (over `env`), when its
    /// parameter types aren't computed from them (#662): its parameters,
    /// types and values, put in by evaluation.
    fn result_type_at(&self, n: usize, ty: &Tm, args: &[(Tm, Mult)]) -> Option<Tm> {
        let vars = (0..n).map(Val::var).collect::<crate::core::Env>();
        let mut v = eval(&self.e.g, &crate::core::Env::new(), ty);
        for (a, _) in args {
            match force(&self.e.g, v) {
                Val::Pi(_, _, _, _, c) => v = crate::core::apply_closure(&self.e.g, &c, eval(&self.e.g, &vars, a)),
                _ => return None,
            }
        }
        Some(quote(&self.e.g, n, &v))
    }

    /// The predicates declared on a class's type (#176), of `x` of type
    /// `ty`, when `ty` is that type read from a dictionary in scope.
    fn class_type_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) -> Vec<String> {
        if self.e.class_type_preds.is_empty() && self.e.g.type_bases.is_empty() {
            return Vec::new();
        }
        let n = env.len();
        let vars = (0..n).map(Val::var).collect::<crate::core::Env>();
        let v = force(&self.e.g, eval(&self.e.g, &vars, ty));
        let Val::Neutral(h, sp) = &v else { return Vec::new() };
        let Some(crate::core::Elim::Field(c, i)) = sp.last() else { return Vec::new() };
        // Its base type's refinement (#360): `Nat`'s, for `i~Nat`.
        let mut out = Vec::new();
        let bases = self.e.g.type_bases.get(&(*c, *i)).cloned().unwrap_or_default();
        if !bases.is_empty() {
            // At the class's arguments and the dictionary in scope.
            let base = Val::Neutral(h.clone(), Rc::new(sp[..sp.len() - 1].to_vec()));
            let dict = quote(&self.e.g, n, &base);
            if let Ok((dt, ds @ Sort::Data(_, _))) = self.term(env, &dict) {
                let Sort::Data(_, sargs) = &ds else { unreachable!() };
                let mut inner: Vec<Ent> = sargs.iter().take(self.class_params(*c)).map(|s| Ent::Ty(s.clone())).collect();
                inner.push(Ent::Term(dt, ds.clone()));
                for b in &bases {
                    out.extend(self.alias_terms(&inner, b, x, xs));
                }
            }
        }
        let Some(preds) = self.e.class_type_preds.get(&(*c, *i)).cloned() else { return out };
        let base = Val::Neutral(h.clone(), Rc::new(sp[..sp.len() - 1].to_vec()));
        let dict = quote(&self.e.g, n, &base);
        let Ok((dt, ds)) = self.term(env, &dict) else { return Vec::new() };
        let Sort::Data(_, sargs) = &ds else { return Vec::new() };
        // The class's parameters, its dictionary, the value.
        let mut inner: Vec<Ent> = sargs.iter().take(self.class_params(*c)).map(|s| Ent::Ty(s.clone())).collect();
        inner.push(Ent::Term(dt, ds.clone()));
        inner.push(Ent::Term(x.to_string(), xs.clone()));
        for p in preds {
            if let Ok((t, Sort::Bool)) = self.term(&inner, &p.tm) {
                out.push(t);
            }
        }
        out
    }

    /// The predicates of the refinement alias `ty` at `x`, as terms.
    fn alias_terms(&mut self, env: &[Ent], ty: &Tm, x: &str, xs: &Sort) -> Vec<String> {
        let (h, args) = ty.spine_cloned();
        let Tm::Def(d) = h else { return Vec::new() };
        let Some(preds) = self.e.alias_preds.get(d).cloned() else { return Vec::new() };
        let mut inner = Vec::new();
        for a in &args {
            // A type the alias captured (`a` of `(x~a, contains xs x)`, at
            // `a` = `Nat` or a type variable) isn't a term: its sort, for the
            // predicates' type arguments.
            inner.push(match self.sort_of(env, a) {
                Ok(s) if self.is_type(a) => Ent::Ty(s),
                sort => match self.term(env, a) {
                    Ok((t, s)) => Ent::Term(t, s),
                    // A known function or dictionary (an instance's, which a
                    // generic signature's refinement captured at a use,
                    // `Seq.size ys` at `s` = `Bytes`): known, as a call's
                    // argument is, so its predicates name the same function.
                    Err(_) => match sort {
                        Ok(s) => Ent::Ty(s),
                        Err(_) => match self.known_fun(env, a) {
                            Some(k) => Ent::Known(k),
                            None => match self.known_dict(env, a) {
                                Ok(Some(k)) => Ent::Known(k),
                                _ => Ent::Opaque("alias argument".into()),
                            },
                        },
                    },
                },
            });
        }
        // The base may be refined too: `(x~a, contains xs x)` at `a` = `Char`.
        let mut out = Vec::new();
        let mut base = self.e.g.defs[d.0 as usize].body.clone();
        for _ in &args {
            base = match base {
                Some(Tm::Lam(_, _, _, b)) => Some((*b).clone()),
                _ => None,
            };
        }
        match base {
            Some(Tm::Var(i)) if i < args.len() => out.extend(self.alias_terms(env, &args[args.len() - 1 - i], x, xs)),
            Some(b) if matches!(b.head(), Tm::Def(_)) => out.extend(self.alias_terms(&inner, &b, x, xs)),
            _ => {}
        }
        inner.push(Ent::Term(x.to_string(), xs.clone()));
        for p in preds {
            if let Ok((t, Sort::Bool)) = self.term(&inner, &p.tm) {
                out.push(t);
            }
        }
        out
    }

    /// Translate a term over the first `lvl` obligation locals.
    fn term_ctx(&mut self, lvl: usize, t: &Tm) -> Tx<(String, Sort)> {
        let mut env = Vec::with_capacity(lvl);
        for k in 0..lvl {
            env.push(Ent::Opaque(format!("@{k}")));
        }
        // Locals are resolved lazily through `@k` markers.
        self.term(&env, t)
    }

    fn resolve(&mut self, env: &[Ent], i: usize) -> Tx<Ent> {
        match env.get(env.len().wrapping_sub(1 + i)) {
            Some(Ent::Opaque(m)) if m.starts_with('@') => {
                let lvl: usize = m[1..].parse().unwrap_or(0);
                self.local(lvl)
            }
            Some(e) => Ok(e.clone()),
            None => out("an unbound variable"),
        }
    }

    fn is_nat_val(&self, ty: &Val) -> bool {
        crate::core::is_nat(&self.e.g, ty)
    }

    fn is_nat_tm(&self, ty: &Tm) -> bool {
        let h = ty.head();
        match h {
            Tm::Def(d) if Some(*d) == self.e.g.well_known.nat => true,
            Tm::Def(d) => match &self.e.g.defs[d.0 as usize].body {
                Some(b) => {
                    let mut b = b;
                    while let Tm::Lam(_, _, _, x) = b {
                        b = x;
                    }
                    self.is_nat_tm(b)
                }
                None => false,
            },
            Tm::Meta(m) => self.e.g.meta(*m).is_some_and(|v| self.is_nat_val(&v)),
            _ => false,
        }
    }

    /// Every result of `f` is a `Nat`: `∀ args. f args >= 0`, instantiated by
    /// Z3 for each `f` term, including those it makes by unfolding definitions.
    fn nat_axiom(&mut self, name: &str, args: &[String]) {
        let ax = if args.is_empty() {
            format!("(>= {name} 0)")
        } else {
            let vars: Vec<String> = (0..args.len()).map(|k| format!("a{k}")).collect();
            let binds: Vec<String> = vars.iter().zip(args).map(|(v, s)| format!("({v} {s})")).collect();
            let app = format!("({name} {})", vars.join(" "));
            format!("(forall ({}) (! (>= {app} 0) :pattern ({app})))", binds.join(" "))
        };
        self.axioms.insert(name.to_string(), ax);
    }

    /// Is `d`'s result `>= 0` for every solver value of its arguments? For
    /// a declared (uninterpreted) `Nat` function, assuming so is consistent.
    /// For a reflected one, its body must be built from non-negative parts
    /// (`0`, `1 + length rest`), with no precondition, and any recursion
    /// structural: the unfolding is then finite on every solver value, so
    /// the claim follows by induction. (`decreasing` recursion may run
    /// forever on values the program can't build, so it gets no axiom.)
    fn nonneg_fn(&self, d: DefId, stack: &mut Vec<DefId>) -> bool {
        let mut ty = self.e.g.defs[d.0 as usize].ty.clone();
        while let Tm::Pi(_, _, _, _, b) = ty {
            ty = (*b).clone();
        }
        if !self.is_nat_tm(&ty) {
            return false;
        }
        if !self.reflected(d) {
            return true;
        }
        let spec = self.e.specs.get(&d);
        if self.e.guessed.contains(&d) || spec.is_some_and(|s| s.measure.is_some() || s.preds.iter().any(|p| !p.is_post)) {
            return false;
        }
        if stack.contains(&d) {
            return true;
        }
        let Some(mut body) = self.e.g.defs[d.0 as usize].body.clone() else { return false };
        while let Tm::Lam(_, _, _, b) = body {
            body = (*b).clone();
        }
        stack.push(d);
        let r = self.nonneg(&body, stack);
        stack.pop();
        r
    }

    /// `t` is `>= 0` for every solver value of its free variables.
    fn nonneg(&self, t: &Tm, stack: &mut Vec<DefId>) -> bool {
        match t {
            Tm::Lit(l @ (Lit::Num(_) | Lit::Big(_))) => l.is_nonneg_int(),
            Tm::PrimApp(Prim::Add | Prim::Mul, xs) => xs.iter().all(|x| self.nonneg(x, stack)),
            Tm::PrimApp(Prim::Len, _) => true,
            Tm::PrimApp(Prim::Par | Prim::Effect(_), xs) => xs.iter().all(|x| self.nonneg(x, stack)),
            Tm::Let(_, _, _, _, b) => self.nonneg(b, stack),
            Tm::Case(_, c) => {
                c.branches.iter().all(|(_, _, b)| matches!(b, Tm::Error) || self.nonneg(b, stack))
                    && c.lits.iter().all(|(_, b)| matches!(b, Tm::Error) || self.nonneg(b, stack))
                    && c.default.as_ref().is_none_or(|b| matches!(b, Tm::Error) || self.nonneg(b, stack))
            }
            Tm::App(..) | Tm::Def(_) => {
                let h = t.head();
                let Tm::Def(d) = h else { return false };
                self.nonneg_fn(*d, stack)
            }
            _ => false,
        }
    }

    /// An element of `a ++ b` is one of `a`'s or one of `b`'s, by where the
    /// index falls: valid facts about `(seq.nth (seq.++ a b) i)`, so Z3 needn't
    /// solve the word equation its sequence theory makes of that element,
    /// whose cost depends on the order of its case splits (and so on how
    /// symbols are spelled). Through nested `++` too.
    fn index_concat(&mut self, s: &str, i: &str) {
        let Some((a, b)) = self.concats.get(s).cloned() else { return };
        if !self.fact_seen.insert(format!("concat-index {s} {i}")) {
            return;
        }
        let la = format!("(seq.len {a})");
        let lb = format!("(seq.len {b})");
        let at = format!("(seq.nth {s} {i})");
        let j = format!("(- {i} {la})");
        self.asserts.push(format!("(=> (and (<= 0 {i}) (< {i} {la})) (= {at} (seq.nth {a} {i})))"));
        self.asserts.push(format!("(=> (and (<= {la} {i}) (< {i} (+ {la} {lb}))) (= {at} (seq.nth {b} {j})))"));
        self.index_concat(&a, i);
        self.index_concat(&b, &j);
    }

    fn nat_fact(&mut self, t: &str) {
        if !self.in_def && self.fact_seen.insert(t.to_string()) {
            self.asserts.push(format!("(>= {t} 0)"));
        }
    }

    fn term(&mut self, env: &[Ent], t: &Tm) -> Tx<(String, Sort)> {
        match t {
            Tm::Var(i) => match self.resolve(env, *i)? {
                Ent::Term(n, s) => Ok((n, s)),
                Ent::Ty(_) | Ent::TyFun(..) | Ent::TyVar(_) => out("a type used as a value"),
                Ent::Known(_) => out("a function used as a value"),
                Ent::Opaque(w) => out(format!("a value the prover can't see ({w})")),
            },
            Tm::Meta(m) => match self.e.g.meta(*m) {
                Some(v) => {
                    let tm = quote(&self.e.g, env.len(), &v);
                    self.term(env, &tm)
                }
                None => out("an unsolved unknown"),
            },
            Tm::Lit(Lit::Num(n)) => Ok((smt_int(*n), Sort::Int)),
            Tm::Lit(Lit::Big(n)) => Ok((smt_int((**n).clone()), Sort::Int)),
            // A constructor or tuple known at compile time, of any size: left
            // out (an obligation that mentions one isn't given its value).
            Tm::Known(_) => out("a value known at compile time"),
            Tm::Lit(Lit::Str(s)) => {
                self.literal_utf8(s.as_bytes());
                Ok((smt_bytes(s.as_bytes()), Sort::Str))
            }
            Tm::Lit(Lit::Bytes(b)) => {
                self.literal_utf8(b);
                Ok((smt_bytes(b), Sort::Seq(Box::new(Sort::Int))))
            }
            Tm::Tuple(xs) => {
                let mut ts = Vec::new();
                let mut ss = Vec::new();
                for x in xs {
                    let (t, s) = self.term(env, x)?;
                    ts.push(t);
                    ss.push(s);
                }
                // A last component that is a tuple: its components (#673).
                if let Some(Sort::Tuple(ws)) = ss.last().filter(|_| ss.len() >= 2).cloned() {
                    if ws.len() >= 2 {
                        ss.pop();
                        let lt = ts.pop().unwrap_or_default();
                        for k in 0..ws.len() {
                            ts.push(format!("({} {lt})", tuple_sel(ws.len(), k)));
                        }
                        ss.extend(ws);
                    }
                }
                self.tuples.insert(ss.len());
                let sort = Sort::Tuple(ss);
                if ts.is_empty() {
                    Ok((tuple_con(0), sort))
                } else {
                    // Qualified, as other constructors are: Z3 can't always
                    // tell a parametric constructor's sort from its arguments.
                    Ok((format!("((as {} {}) {})", tuple_con(ts.len()), sort.render(self.e), ts.join(" ")), sort))
                }
            }
            Tm::Proj(x, i, rest) => {
                let (xt, xs) = self.term(env, x)?;
                match xs {
                    // The rest of a longer tuple: a tuple of its components (#673).
                    Sort::Tuple(ss) if *rest && ss.len() > i + 1 => {
                        let rs = ss[*i..].to_vec();
                        self.tuples.insert(rs.len());
                        let parts: Vec<String> = (*i..ss.len()).map(|k| format!("({} {xt})", tuple_sel(ss.len(), k))).collect();
                        let sort = Sort::Tuple(rs);
                        Ok((format!("((as {} {}) {})", tuple_con(ss.len() - i), sort.render(self.e), parts.join(" ")), sort))
                    }
                    Sort::Tuple(ss) => {
                        let s = ss.get(*i).cloned().ok_or_else(|| Outside("a bad projection".into()))?;
                        let t = format!("({} {xt})", tuple_sel(ss.len(), *i));
                        Ok((t, s))
                    }
                    _ => out("a projection from a non-tuple"),
                }
            }
            Tm::Field(x, c, i, _) => {
                // A field of a value built here (a known instance's
                // dictionary): the value given for it.
                if !matches!(self.e.g.cons[c.0 as usize].fields[*i].3, Tm::Pi(..)) {
                    if let Some(a) = self.built_field(x, *c, *i) {
                        return self.term(env, &a);
                    }
                }
                let (xt, xs) = self.term(env, x)?;
                // A string is its bytes (#546, #170).
                if xs == Sort::Str {
                    return Ok((xt, Sort::Seq(Box::new(Sort::Int))));
                }
                let Sort::Data(id, sargs) = &xs else { return out("a field of a non-record") };
                if *id != self.e.g.cons[c.0 as usize].ty {
                    return Err(self.ill_sorted());
                }
                let fs = self.con_fields(*c, &self.sort_env(self.e.g.cons[c.0 as usize].ty, sargs))?;
                let Some((_, s)) = fs.iter().find(|(k, _)| k == i).cloned() else {
                    return out("a type-valued field");
                };
                let t = format!("({} {xt})", sel_sym(self.e, *c, *i));
                // A field has what its declared type says (`value_terms`), at
                // the sorts of the type's parameters: a local of the record's
                // type has more, with its type's arguments.
                if !self.in_def && self.fact_seen.insert(t.clone()) {
                    let rec = self.e.g.cons[c.0 as usize].ty;
                    let mut fenv = self.sort_env(rec, sargs);
                    let senv = fenv.clone();
                    for j in 0..*i {
                        match fs.iter().find(|(k, _)| *k == j) {
                            Some((_, js)) => fenv.push(Ent::Term(format!("({} {xt})", sel_sym(self.e, *c, j)), js.clone())),
                            None => {
                                let js = self.type_field_sort(*c, j, &senv);
                                fenv.push(Ent::Ty(js));
                            }
                        }
                    }
                    let fty = self.e.g.cons[c.0 as usize].fields[*i].3.clone();
                    let facts = self.value_terms(&fenv, &fty, &t, &s);
                    self.asserts.extend(facts);
                    if let Sort::Data(id, _) = &s {
                        self.real_values.push((t.clone(), *id));
                    }
                }
                Ok((t, s))
            }
            Tm::Let(_, _, ty, v, b) => {
                // Substituted rather than `let`-bound, so terms collected inside
                // (postconditions of calls) stay closed.
                let mut env2 = env.to_vec();
                // A type (an instance's class parameter by its name, #161).
                if self.is_type(ty) {
                    env2.push(Ent::Ty(self.sort_of(env, v)?));
                } else {
                    let (vt, vs) = self.term(env, v)?;
                    env2.push(Ent::Term(vt, vs));
                }
                self.term(&env2, b)
            }
            Tm::App(..) | Tm::Def(_) | Tm::Con(_) => self.app(env, t),
            Tm::ConApp(c, args) => {
                let args: Vec<Tm> = args.clone();
                self.con_app(env, *c, &args)
            }
            Tm::PrimApp(Prim::Forall, args) if args.len() == 1 => self.forall(env, &args[0]),
            Tm::PrimApp(Prim::Effect(id), args) if args.len() == 1 => self.effect(env, *id, &args[0]),
            Tm::PrimApp(p, args) => self.prim(env, p, args),
            Tm::Case(s, c) => self.case(env, s, c),
            Tm::Lam(..) => out("a lambda"),
            Tm::Error => Err(Outside::type_error()),
            _ => out("a type used as a value"),
        }
    }

    /// A term of sort `have` where one of sort `want` is needed: a type
    /// error the type checker reported, whose term it kept (§7.3). Sorts
    /// are the same for Z3 if they are written the same (a string is its
    /// bytes).
    fn expect(&self, have: &Sort, want: &Sort) -> Tx<()> {
        if have == want || have.render(self.e) == want.render(self.e) {
            Ok(())
        } else {
            Err(self.ill_sorted())
        }
    }

    /// A term whose parts' sorts don't fit its place: a type error (§7.3),
    /// counted, since a program without type errors has none.
    fn ill_sorted(&self) -> Outside {
        self.e.ill_sorted.set(self.e.ill_sorted.get() + 1);
        Outside::type_error()
    }

    /// A predicate: a term of sort `Bool`.
    fn prop(&mut self, env: &[Ent], t: &Tm) -> Tx<String> {
        let (t, s) = self.term(env, t)?;
        self.expect(&s, &Sort::Bool)?;
        Ok(t)
    }

    fn sort_env(&self, id: TyId, sargs: &[Sort]) -> Vec<Ent> {
        let params = &self.e.g.tys[id.0 as usize].params;
        let mut k = 0;
        params
            .iter()
            .map(|(_, t)| {
                if self.is_type(t) {
                    k += 1;
                    Ent::Ty(sargs.get(k - 1).cloned().unwrap_or(Sort::Int))
                } else {
                    Ent::Opaque("value parameter".into())
                }
            })
            .collect()
    }

    /// The value given for field `i` of constructor `c` where `x` is that
    /// constructor applied (`C p… f…`).
    fn built_field(&self, x: &Tm, c: ConId, i: usize) -> Option<Tm> {
        let np = self.e.g.arity_ty(self.e.g.cons[c.0 as usize].ty);
        match x {
            Tm::ConApp(c2, args) if *c2 == c => args.get(np + i).cloned(),
            Tm::App(..) => {
                let mut args = Vec::new();
                let mut h = x;
                while let Tm::App(f, a, _, _, _) = h {
                    args.push(a);
                    h = f;
                }
                args.reverse();
                match h {
                    Tm::Con(c2) if *c2 == c => args.get(np + i).map(|a| Tm::clone(a)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn con_app(&mut self, env: &[Ent], c: ConId, args: &[Tm]) -> Tx<(String, Sort)> {
        let e = self.e;
        let wk = &e.g.well_known;
        if Some(c) == wk.true_con {
            return Ok(("true".into(), Sort::Bool));
        }
        if Some(c) == wk.false_con {
            return Ok(("false".into(), Sort::Bool));
        }
        let ci = self.e.g.cons[c.0 as usize].fields.clone();
        let id = self.e.g.cons[c.0 as usize].ty;
        let np = self.e.g.arity_ty(id);
        if args.len() < np + ci.len() {
            return out("a partially applied constructor");
        }
        // A string is its bytes (#546, #170).
        if Some(id) == wk.string {
            let (t, s) = self.term(env, &args[np])?;
            self.expect(&s, &Sort::Seq(Box::new(Sort::Int)))?;
            return Ok((t, Sort::Str));
        }
        let sort = {
            let ptys: Vec<Tm> = args[..np].to_vec();
            self.ty_sort(env, id, &ptys)?
        };
        let Sort::Data(_, sargs) = &sort else { return out("a constructor of an abstract type") };
        let fs = self.con_fields(c, &self.sort_env(id, sargs))?;
        // A class's type is a sort of its own in its dictionary's fields
        // (`Seq.Elem s`), which a known type (`Int`) can't stand for: a
        // dictionary whose functions use its class's types can't be built.
        for k in 0..ci.len() {
            if self.e.g.is_type_field(c, k) {
                if let Sort::Unin(n, _) = self.type_field_sort(c, k, &self.sort_env(id, sargs)) {
                    if fs.iter().any(|(_, s)| s.mentions(&n)) {
                        return out("a dictionary whose functions use its class's types");
                    }
                }
            }
        }
        let mut ts = Vec::new();
        for (k, s) in &fs {
            let t = match s {
                Sort::Fun(..) => self.fun_value(env, &args[np + k], s)?,
                _ => {
                    let (t, ts) = self.term(env, &args[np + k])?;
                    self.expect(&ts, s)?;
                    t
                }
            };
            ts.push(t);
        }
        let head = format!("(as {} {})", con_sym(self.e, c), sort.render(self.e));
        let t = if ts.is_empty() { head } else { format!("({head} {})", ts.join(" ")) };
        Ok((t, sort))
    }

    fn app(&mut self, env: &[Ent], t: &Tm) -> Tx<(String, Sort)> {
        let mut args: Vec<(Tm, Mult)> = Vec::new();
        let mut h = t;
        while let Tm::App(f, a, _, m, _) = h {
            args.push(((**a).clone(), *m));
            h = f;
        }
        args.reverse();
        match h {
            Tm::Con(c) => {
                let a: Vec<Tm> = args.into_iter().map(|x| x.0).collect();
                self.con_app(env, *c, &a)
            }
            Tm::Def(d) => self.def_app(env, *d, &args),
            Tm::Var(i) => match self.resolve(env, *i)? {
                Ent::Known(k) => {
                    let f = self.known.get(&k).cloned().ok_or_else(|| Outside("an unknown function".into()))?;
                    self.apply_known(env, &f, &args)
                }
                Ent::Term(ft, s @ Sort::Fun(..)) => self.select(env, &ft, &s, &args),
                _ => out("an application of a non-function"),
            },
            Tm::Lam(..) => self.apply_known(env, h, &args),
            // A function from a value built here (a known instance's
            // dictionary, `Seq.size` at `Seq (Array Int)`): that function
            // applied, without building the value.
            Tm::Field(x, c, i, _) if self.built_field(x, *c, *i).is_some() => {
                let mut app = self.built_field(x, *c, *i).unwrap();
                for (a, m) in args {
                    let icit = if m == Mult::Zero { crate::core::Icit::Impl } else { crate::core::Icit::Expl };
                    app = Tm::App(Rc::new(app), Rc::new(a), icit, m, crate::core::Pos::NONE);
                }
                self.term(env, &app)
            }
            Tm::Field(..) | Tm::Proj(..) | Tm::Case(..) | Tm::Let(..) => {
                let (ft, s) = self.term(env, h)?;
                self.select(env, &ft, &s, &args)
            }
            Tm::Meta(m) if self.e.g.meta(*m).is_some() => {
                let z = self.zonk(env.len(), t);
                if has_meta(&z) {
                    return out("an unsolved unknown");
                }
                self.term(env, &z)
            }
            _ => out("an unsupported application"),
        }
    }

    /// The sorts of a `forall`'s variables, over the obligation's locals.
    fn forall_sorts(&mut self, lvl: usize, pi: &Tm) -> Tx<Vec<Sort>> {
        let mut inner: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let mut out_ = Vec::new();
        let mut t = pi.clone();
        while let Tm::Pi(_, _, _, a, b) = t {
            let s = self.sort_of(&inner, &a)?;
            inner.push(Ent::Term(String::new(), s.clone()));
            out_.push(s);
            t = (*b).clone();
        }
        Ok(out_)
    }

    /// A `forall`'s body at the given values, if its variables have those
    /// sorts, and what the values must satisfy to be in its variables'
    /// types (`domain_terms`): to be assumed of them where the `forall` is
    /// proved, and the condition under which it holds of them where it is
    /// a premise (#115).
    fn forall_body_at(&mut self, lvl: usize, pi: &Tm, names: &[String], sorts: &[Sort]) -> Tx<Option<(String, Vec<String>)>> {
        let mut inner: Vec<Ent> = (0..lvl).map(|k| Ent::Opaque(format!("@{k}"))).collect();
        let mut guards = Vec::new();
        let mut t = pi.clone();
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = t {
            let s = self.sort_of(&inner, &a)?;
            if sorts.get(k) != Some(&s) {
                return Ok(None);
            }
            guards.extend(self.domain_terms(&inner, &a, &names[k], &s));
            inner.push(Ent::Term(names[k].clone(), s));
            t = (*b).clone();
            k += 1;
        }
        if k != sorts.len() {
            return Ok(None);
        }
        let (bt, bs) = self.term(&inner, &t)?;
        Ok((bs == Sort::Bool).then_some((bt, guards)))
    }

    /// A `forall` premise at the values `forall_body_at` gave it: its body
    /// where they are in its variables' types.
    fn premise_at(&mut self, lvl: usize, pi: &Tm, names: &[String], sorts: &[Sort]) -> Option<String> {
        let (b, guards) = self.forall_body_at(lvl, pi, names, sorts).ok()??;
        Some(implies(&guards, b))
    }

    /// Proving `xs == ys` for arrays or bytes (#75): they are equal if their
    /// lengths are and so are their elements at a fresh index `w`, which is
    /// how an equality follows from a `forall` over the indexes. The
    /// disjunction to add to the goal, and each `forall` in scope over one
    /// `Nat` or `Int` given at `w` when `w` is an index. Z3 alone doesn't
    /// conclude that two sequences are equal from their elements.
    fn extensional(&mut self, lvl: usize, goal: &Tm, facts: &[Val]) -> Tx<Option<(String, Vec<String>)>> {
        let Tm::PrimApp(Prim::Eq, sides) = goal else { return Ok(None) };
        if sides.len() != 2 {
            return Ok(None);
        }
        let (a, sa) = self.term_ctx(lvl, &sides[0])?;
        if !matches!(sa, Sort::Seq(_)) {
            return Ok(None);
        }
        let (b, sb) = self.term_ctx(lvl, &sides[1])?;
        self.expect(&sb, &sa)?;
        let w = "|ext.index|".to_string();
        self.consts.push(format!("(declare-const {w} Int)"));
        let inside = format!("(and (<= 0 {w}) (< {w} (seq.len {a})))");
        let ext = format!("(and (= (seq.len {a}) (seq.len {b})) (=> {inside} (= (seq.nth {a} {w}) (seq.nth {b} {w}))))");
        let (nat, int) = (self.wk().nat, self.wk().int);
        let mut at = Vec::new();
        for f in facts {
            let Tm::PrimApp(Prim::Forall, fa) = quote(&self.e.g, lvl, f) else { continue };
            let [pi] = fa.as_slice() else { continue };
            let Tm::Pi(_, _, _, dom, body) = pi else { continue };
            // One variable, whose every value in range is an index: a
            // refinement of `Int` would hold of fewer.
            let index = match self.zonk(lvl, dom) {
                Tm::Def(d) => Some(d) == nat,
                Tm::TyCon(t) => Some(t) == int,
                Tm::TyConApp(t, ref args) => args.is_empty() && Some(t) == int,
                _ => false,
            };
            if !index || matches!(**body, Tm::Pi(..)) {
                continue;
            }
            if let Some(b) = self.premise_at(lvl, pi, std::slice::from_ref(&w), &[Sort::Int]) {
                at.push(format!("(=> {inside} {b})"));
            }
        }
        Ok(Some((ext, at)))
    }

    /// `forall x y : …` (#632): proved (so Z3 refutes its negation with
    /// fresh values, without quantifier instantiation), and assumed only to
    /// check a counterexample (#77). Its variables range over their types:
    /// a `Nat` is non-negative and a refinement's predicates hold (#112).
    fn forall(&mut self, env: &[Ent], pi: &Tm) -> Tx<(String, Sort)> {
        let d = self.binder_mark();
        let mut inner = env.to_vec();
        let mut binds = Vec::new();
        let mut guards = Vec::new();
        let mut t = pi.clone();
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = t {
            let s = self.sort_of(&inner, &a)?;
            let n = format!("|all{d}.{k}|");
            binds.push(format!("({n} {})", s.render(self.e)));
            guards.extend(self.domain_terms(&inner, &a, &n, &s));
            inner.push(Ent::Term(n, s));
            t = (*b).clone();
            k += 1;
        }
        let saved = self.in_def;
        self.in_def = true;
        self.lam_depth += 1;
        let r = self.term(&inner, &t);
        self.lam_depth -= 1;
        self.in_def = saved;
        let (bt, bs) = r?;
        if bs != Sort::Bool || binds.is_empty() {
            return out("a `forall` that is not a `Bool`");
        }
        let all = format!("(forall ({}) {})", binds.join(" "), implies(&guards, bt));
        Ok((name_binders(&all, &d), Sort::Bool))
    }

    /// Apply the function value `ft` (of sort `s`) to `args` (#630).
    fn select(&mut self, env: &[Ent], ft: &str, s: &Sort, args: &[(Tm, Mult)]) -> Tx<(String, Sort)> {
        let mut app = ft.to_string();
        let mut sort = s.clone();
        let mut ats = Vec::new();
        for (a, m) in args {
            if *m == Mult::Zero {
                continue;
            }
            let Sort::Fun(p, r) = sort else { return out("an application of a non-function") };
            // A function argument is a function value: a lambda is Z3's
            // `lambda`, inside a reflected body too (#231).
            let arg = if matches!(*p, Sort::Fun(..)) {
                self.fun_value(env, a, &p)
            } else {
                self.term(env, a).and_then(|(t, s)| self.expect(&s, &p).map(|_| t))
            };
            let at = match arg {
                Ok(at) => at,
                // A function value the prover can't represent (a lambda, a
                // partial application), given to a function it knows only by
                // its type: a fresh value of its sort, of which nothing is
                // assumed. Its refinements are checked where it is given, and
                // the call's result has what the callee's type promises of
                // every argument. Not where the value depends on bound
                // variables (a reflected body, a lambda's, a `forall`'s), as
                // one constant would stand for all of them.
                Err(_) if matches!(*p, Sort::Fun(..)) && !self.in_def => {
                    let n = sym(&format!("fun#{}", self.fun_args));
                    self.fun_args += 1;
                    self.consts.push(format!("(declare-const {n} {})", p.render(self.e)));
                    n
                }
                Err(e) => return Err(e),
            };
            app = format!("(select {app} {at})");
            ats.push((at, *p));
            sort = *r;
        }
        // A local function of a refined type: its postconditions (#580).
        if !self.in_def && !matches!(sort, Sort::Fun(..)) && self.fun_tys.contains_key(ft) && self.post_seen.insert(app.clone()) {
            let ft = ft.to_string();
            self.fun_post_facts(args, &ats, &ft, &app, &sort);
        }
        Ok((app, sort))
    }

    /// `arg` as a function value of sort `want` (#630): a parameter or field
    /// already is one; a lambda becomes Z3's `lambda`, and anything else (a
    /// named function, a partial application, a local function) one that
    /// applies it.
    fn fun_value(&mut self, env: &[Ent], arg: &Tm, want: &Sort) -> Tx<String> {
        if !matches!(want, Sort::Fun(..)) {
            return out("a function value of a non-function type");
        }
        let mut ps = Vec::new();
        let mut w = want;
        while let Sort::Fun(p, r) = w {
            ps.push((**p).clone());
            w = r;
        }
        let arg = self.zonk(env.len(), arg);
        if let Tm::Var(i) = &arg {
            match self.resolve(env, *i)? {
                Ent::Term(t, Sort::Fun(..)) => return Ok(t),
                Ent::Known(k) => {
                    let f = self.known.get(&k).cloned().ok_or_else(|| Outside("an unknown function".into()))?;
                    return self.fun_value(&[], &f, want);
                }
                _ => {}
            }
        }
        let d = self.binder_mark();
        let names: Vec<String> = (0..ps.len()).map(|k| format!("|lam{d}.{k}|")).collect();
        let mut inner = env.to_vec();
        let mut body = arg;
        let mut used = 0;
        while used < ps.len() {
            let Tm::Lam(_, m, _, b) = &body else { break };
            if *m == Mult::Zero {
                inner.push(Ent::Opaque("erased parameter".into()));
            } else {
                inner.push(Ent::Term(names[used].clone(), ps[used].clone()));
                used += 1;
            }
            let b = (**b).clone();
            body = b;
        }
        let rest = ps.len() - used;
        if rest > 0 {
            // Apply what is left to the remaining parameters.
            let mut app = crate::stage::shift(&body, rest, 0);
            for k in 0..rest {
                inner.push(Ent::Term(names[used + k].clone(), ps[used + k].clone()));
                app = Tm::App(Rc::new(app), Rc::new(Tm::Var(rest - 1 - k)), crate::core::Icit::Expl, Mult::Many, crate::core::Pos::NONE);
            }
            body = app;
        } else if matches!(body, Tm::Lam(..)) {
            return out("a lambda with more parameters than its type");
        }
        let saved = self.in_def;
        self.in_def = true;
        self.lam_depth += 1;
        let r = self.term(&inner, &body);
        self.lam_depth -= 1;
        self.in_def = saved;
        let (bt, _) = r?;
        let mut v = bt;
        for (n, s) in names.iter().zip(&ps).rev() {
            v = format!("(lambda (({n} {})) {v})", s.render(self.e));
        }
        Ok(name_binders(&v, &d))
    }

    /// A placeholder for the binders of a lambda or `forall` being
    /// translated, replaced by `name_binders` once its body is.
    fn binder_mark(&mut self) -> String {
        self.binder_marks += 1;
        format!("?{}", self.binder_marks)
    }

    /// Is this binder's type a class's dictionary (#615)?
    fn is_dict_ty(&self, t: &Tm) -> bool {
        let h = t.head();
        match h {
            Tm::TyCon(id) | Tm::TyConApp(id, _) => self.e.class_defs.contains_key(id),
            Tm::Meta(m) => matches!(self.e.g.meta(*m).map(|v| force(&self.e.g, v)), Some(Val::TyCon(id, _)) if self.e.class_defs.contains_key(&id)),
            _ => false,
        }
    }

    /// The position of a class function's dictionary binder: the one its
    /// body reads its field from. Its own class clauses' dictionaries are
    /// implicit too, and come first when it takes a class's parameter
    /// explicitly (the class's dictionary follows that parameter).
    fn dict_pos(&self, d: DefId) -> Option<usize> {
        let mut body = self.e.g.defs[d.0 as usize].body.as_ref();
        let mut k = 0;
        while let Some(Tm::Lam(_, _, _, b)) = body {
            body = Some(&**b);
            k += 1;
        }
        if let Some(mut r) = body {
            while let Tm::App(f, ..) = r {
                r = f;
            }
            if let Tm::Field(x, _, _, _) = r {
                if let Tm::Var(j) = **x {
                    if j < k {
                        return Some(k - 1 - j);
                    }
                }
            }
        }
        // Without a body: the first dictionary binder.
        let mut t = self.e.g.defs[d.0 as usize].ty.clone();
        let mut k = 0;
        while let Tm::Pi(_, m, i, a, b) = t {
            if m == Mult::Many && i == crate::core::Icit::Impl && self.is_dict_ty(&a) {
                return Some(k);
            }
            t = (*b).clone();
            k += 1;
        }
        None
    }

    /// `f x …` for class function `f` (`d`) given a known instance's
    /// dictionary: the instance's own function, applied to the same
    /// arguments, taken from the dictionary's definition.
    fn member_app(&mut self, env: &[Ent], d: DefId, args: &[(Tm, Mult)], inner: &[Ent]) -> Tx<Option<(String, Sort)>> {
        let Some(pos) = self.dict_pos(d) else { return Ok(None) };
        let Some(Ent::Known(key)) = inner.get(pos) else { return Ok(None) };
        let Some(dict) = self.known.get(key).cloned() else { return Ok(None) };
        // The dictionary: an instance's function applied to its arguments.
        let (h, dargs) = dict.spine_cloned();
        let Tm::Def(dd) = h else { return Ok(None) };
        if !self.e.dict_defs.contains(dd) {
            return Ok(None);
        }
        let Some(mut body) = self.e.g.defs[dd.0 as usize].body.clone() else { return Ok(None) };
        for _ in 0..dargs.len() {
            match body {
                Tm::Lam(_, _, _, b) => body = (*b).clone(),
                _ => return Ok(None),
            }
        }
        // Its field for this function.
        let name = self.e.g.defs[d.0 as usize].name.clone();
        let (hb, fields) = body.spine_cloned();
        let (con, mut all) = match hb {
            Tm::Con(c) => (*c, fields),
            Tm::ConApp(c, v) => (*c, v.clone()),
            _ => return Ok(None),
        };
        let cty = self.e.g.cons[con.0 as usize].ty;
        let np = self.e.g.arity_ty(cty);
        if all.len() < np {
            return Ok(None);
        }
        all.drain(..np);
        let Some(cd) = self.e.class_defs.get(&cty) else { return Ok(None) };
        // The dictionary's fields: the class's types (#133), then its functions.
        let Some(fi) = cd.methods().iter().position(|m| **m == *name).map(|k| k + cd.method_offset()) else { return Ok(None) };
        let Some(field) = all.get(fi).cloned() else { return Ok(None) };
        // The environment: the dictionary's arguments, then the call's explicit ones.
        let mut ienv: Vec<Ent> = Vec::new();
        let mut dty = self.e.g.defs[dd.0 as usize].ty.clone();
        let stored = self.dict_args.get(key).cloned();
        for (j, a) in dargs.iter().enumerate() {
            let Tm::Pi(_, _, _, dom, cod) = dty else { return Ok(None) };
            let e = if let Some(e) = stored.as_ref().and_then(|s| s.get(j)) {
                e.clone()
            } else if self.is_kind(&dom) {
                self.ty_fun(env, a).ok_or_else(|| Outside("a type constructor the prover can't see".into()))?
            } else if self.is_type(&dom) {
                Ent::Ty(self.sort_of(env, a)?)
            } else if let Some(k2) = self.is_dict_ty(&dom).then(|| self.known_fun(env, a)).flatten() {
                Ent::Known(k2)
            } else {
                let (at, s) = self.term(env, a)?;
                Ent::Term(at, s)
            };
            ienv.push(e);
            dty = (*cod).clone();
        }
        // The function's own type arguments (M25: a polymorphic field takes
        // them first), then its explicit ones.
        let mut tyargs = Vec::new();
        {
            let mut t = self.e.g.defs[d.0 as usize].ty.clone();
            let mut k = 0;
            while let Tm::Pi(x, _, _, a, b) = t {
                if k >= pos {
                    break;
                }
                if self.is_type(&a) && !cd.params.iter().any(|p| **p == *x) {
                    tyargs.push(inner[k].clone());
                }
                t = (*b).clone();
                k += 1;
            }
        }
        let field_tys = {
            let mut n = 0;
            let mut f = &field;
            while let Tm::Lam(_, Mult::Zero, crate::core::Icit::Impl, b) = f {
                n += 1;
                f = b;
            }
            n
        };
        // A polymorphic field's type parameters are bound to the call's
        // type arguments directly (its body refers to the dictionary's own).
        let mut field = field;
        if field_tys == tyargs.len() {
            for _ in 0..field_tys {
                let Tm::Lam(_, _, _, b) = field else { unreachable!() };
                field = (*b).clone();
            }
            ienv.extend(tyargs);
        }
        // The arguments after the dictionary, and the explicit ones before
        // it (a class's parameter passed explicitly, #161, among them: the
        // dictionary's field takes it too). The function's own class clauses'
        // dictionaries come first, wherever they are: the class's follows a
        // class's parameter passed explicitly, so a clause may precede it,
        // or, when the clause mentions that parameter, follow it after the
        // call's explicit arguments.
        let mut rest: Vec<Ent> = Vec::new();
        {
            let mut t = self.e.g.defs[d.0 as usize].ty.clone();
            let mut k = 0;
            let mut clauses = 0;
            while let Tm::Pi(_, m, i, a, b) = t {
                if k != pos && m == Mult::Many && i == crate::core::Icit::Impl && self.is_dict_ty(&a) {
                    let Some(e) = inner.get(k) else { break };
                    rest.insert(clauses, e.clone());
                    clauses += 1;
                } else if k > pos || (k < pos && i == crate::core::Icit::Expl) {
                    let Some(e) = inner.get(k) else { break };
                    rest.push(e.clone());
                }
                t = (*b).clone();
                k += 1;
            }
            rest.extend(inner.get(k..).unwrap_or_default().iter().cloned());
        }
        // The function's own class clauses' dictionaries (`Seq s` of
        // `fn weigh by xs : Seq s, …`), the first arguments after the
        // class's: bound directly too, as its body may use its type
        // parameters.
        let mut rest = rest.into_iter();
        while let Tm::Lam(_, Mult::Many, crate::core::Icit::Impl, b) = &field {
            let Some(e) = rest.next() else { break };
            ienv.push(e);
            field = (**b).clone();
        }
        let rest: Vec<Ent> = rest.collect();
        let n = rest.len();
        ienv.extend(rest);
        let mut app = crate::stage::shift(&field, n, 0);
        for j in 0..n {
            app = Tm::App(Rc::new(app), Rc::new(Tm::Var(n - 1 - j)), crate::core::Icit::Expl, Mult::Many, crate::core::Pos::NONE);
        }
        let _ = args;
        self.term(&ienv, &app).map(Some)
    }

    /// Should `d`'s definition be visible to the solver (#506)?
    fn reflected(&self, d: DefId) -> bool {
        let info = &self.e.g.defs[d.0 as usize];
        // `opaque` covers `partial` functions and builtins.
        info.body.is_some()
            && !info.opaque
            && (*info.module == *self.user || self.e.transparent.contains(&d))
            && !self.large_constant(d)
    }

    /// A constant whose value is `array.from_list` of a list literal, its
    /// elements closed terms the solver can see: declared, with its length
    /// and each element asserted (#638). Equations on `seq.nth` are cheap for
    /// Z3 where the value as a term (`seq.++` of 2,000 units) is not.
    fn array_table(&mut self, d: DefId, rs: &Sort) -> Tx<Option<(String, Sort)>> {
        let name = {
            let info = &self.e.g.defs[d.0 as usize];
            sym(&format!("{}.{}", info.module, info.name))
        };
        if self.funs.contains_key(&name) {
            return Ok(Some((name, rs.clone())));
        }
        let here = self.e.uid;
        let found = TABLES.with(|t| {
            let mut t = t.borrow_mut();
            if t.0 != here {
                *t = (here, BTreeMap::new());
            }
            t.1.get(&name).cloned()
        });
        let (delta, facts) = match found {
            Some(x) => x,
            None => {
                // Translated once, in an empty builder, and replayed in each
                // query's (as `define_shared` does for definitions).
                let saved = (
                    std::mem::take(&mut self.datatypes),
                    std::mem::take(&mut self.tuples),
                    std::mem::take(&mut self.sorts),
                    std::mem::take(&mut self.funs),
                    std::mem::take(&mut self.asserts),
                    std::mem::take(&mut self.table_facts),
                    std::mem::take(&mut self.tested),
                );
                let r = self.table_fresh(d, rs);
                let delta = Delta {
                    datatypes: std::mem::replace(&mut self.datatypes, saved.0).into_iter().collect(),
                    tuples: std::mem::replace(&mut self.tuples, saved.1).into_iter().collect(),
                    sorts: std::mem::replace(&mut self.sorts, saved.2).into_iter().collect(),
                    funs: std::mem::replace(&mut self.funs, saved.3).into_iter().collect(),
                    asserts: std::mem::replace(&mut self.asserts, saved.4),
                    tested: std::mem::replace(&mut self.tested, saved.6).into_iter().collect(),
                    ..Delta::default()
                };
                let facts = std::mem::replace(&mut self.table_facts, saved.5);
                match r? {
                    Some(_) => {}
                    None => return Ok(None),
                }
                TABLES.with(|t| t.borrow_mut().1.insert(name.clone(), (delta.clone(), facts.clone())));
                (delta, facts)
            }
        };
        self.datatypes.extend(delta.datatypes);
        self.tuples.extend(delta.tuples);
        self.sorts.extend(delta.sorts);
        for (k, v) in delta.funs {
            self.funs.entry(k).or_insert(v);
        }
        self.asserts.extend(delta.asserts);
        self.tested.extend(delta.tested);
        self.table_facts.extend(facts);
        Ok(Some((name, rs.clone())))
    }

    fn table_fresh(&mut self, d: DefId, rs: &Sort) -> Tx<Option<(String, Sort)>> {
        let info = &self.e.g.defs[d.0 as usize];
        if matches!(info.ty, Tm::Pi(..)) || info.opaque || !(*info.module == *self.user || self.e.transparent.contains(&d)) {
            return Ok(None);
        }
        let Some(body) = info.body.clone() else { return Ok(None) };
        let name = sym(&format!("{}.{}", info.module, info.name));
        let table = if matches!(rs, Sort::Seq(_)) { array_literal(self.e, &body) } else { None };
        let Some(elems) = table else {
            // Any other large constant: its value as one equation, also only
            // in the full query.
            if !self.large_constant(d) || !closed(&body, 0) {
                return Ok(None);
            }
            if !self.funs.contains_key(&name) {
                self.funs.insert(name.clone(), format!("(declare-fun {name} () {})", rs.render(self.e)));
                let saved = self.in_def;
                self.in_def = true;
                let r = self.term(&[], &body);
                self.in_def = saved;
                // Not a value with a type error (§7.3).
                if let Ok((t, s)) = r {
                    if self.expect(&s, rs).is_ok() {
                        self.table_facts.push(format!("(assert (= {name} {t}))\n"));
                    }
                }
            }
            return Ok(Some((name, rs.clone())));
        };
        if !self.funs.contains_key(&name) {
            self.funs.insert(name.clone(), format!("(declare-fun {name} () {})", rs.render(self.e)));
            self.asserts.push(format!("(= (seq.len {name}) {})", elems.len()));
            let saved = self.in_def;
            self.in_def = true;
            let elem = match rs {
                Sort::Seq(e) => (**e).clone(),
                _ => Sort::Int,
            };
            for (i, x) in elems.iter().enumerate() {
                match self.term(&[], x) {
                    Ok((t, s)) if self.expect(&s, &elem).is_ok() => {
                        self.table_facts.push(format!("(assert (= (seq.nth {name} {i}) {t}))\n"))
                    }
                    _ => break,
                }
            }
            self.in_def = saved;
        }
        Ok(Some((name, rs.clone())))
    }

    /// A constant whose value is large: not reflected as a definition (a
    /// 2,000-unit term in a recursive definition is slow for Z3) but given
    /// as an equation in the full query (#638).
    fn large_constant(&self, d: DefId) -> bool {
        let info = &self.e.g.defs[d.0 as usize];
        !matches!(info.ty, Tm::Pi(..)) && info.body.as_ref().is_some_and(|b| tm_size(b, LARGE_CONSTANT) >= LARGE_CONSTANT)
    }

    /// A call with effects (§7.1): outside a reflected body, a constant of
    /// its own, `id`'s, with the callee's postconditions where `def_app`
    /// can give them (`effect`); otherwise, the call itself, as the body
    /// says (the body's callers' calls are values of their own).
    fn effect(&mut self, env: &[Ent], id: u32, x: &Tm) -> Tx<(String, Sort)> {
        let mut x = x;
        while let Tm::PrimApp(Prim::Effect(_), a) = x {
            match &a[..] {
                [y] => x = y,
                _ => break,
            }
        }
        if self.in_def {
            return self.term(env, x);
        }
        let name = format!("|effect#{id}|");
        if let Some(s) = self.effect_sorts.get(&name) {
            return Ok((name, s.clone()));
        }
        // Only a call of a named function, which `def_app` translates
        // first, takes the constant: not a call inside a local function's
        // arguments.
        let flag = matches!(x.head(), Tm::Def(_)).then(|| name.clone());
        let saved = std::mem::replace(&mut self.effect, flag);
        let r = self.term(env, x);
        self.effect = saved;
        let (_, s) = r?;
        if !self.funs.contains_key(&name) {
            self.funs.insert(name.clone(), format!("(declare-fun {name} () {})", s.render(self.e)));
        }
        self.effect_sorts.insert(name.clone(), s.clone());
        Ok((name, s))
    }

    fn def_app(&mut self, env: &[Ent], d: DefId, args: &[(Tm, Mult)]) -> Tx<(String, Sort)> {
        // A call with effects whose value is a constant of its own: this one.
        let effect = self.effect.take();
        let info = &self.e.g.defs[d.0 as usize];
        let qualified = format!("{}.{}", info.module, info.name);
        let ty = info.ty.clone();
        let info_ty = ty.clone();
        // Walk the binders: type arguments pick the instance, values are arguments.
        let mut tys = Vec::new();
        let mut funs: Vec<String> = Vec::new();
        let mut vals = Vec::new();
        let mut post_env = Vec::new();
        let mut inner: Vec<Ent> = Vec::new();
        let dpos = if self.e.class_methods.contains(&d) { self.dict_pos(d) } else { None };
        // The values of arguments that hold types (`ts~Types`, #662), for the
        // parameter types computed from them; unknowns for the others.
        let mut type_vals: Vec<Val> = Vec::new();
        let mut computed = false;
        let mut t = ty;
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = t.clone() {
            let Some((arg, _)) = args.get(k) else {
                return out(match self.e.hidden_home(&self.user, &qualified) {
                    Some(home) => format!("a partial application of a private function of `{home}`"),
                    None => format!("a partial application of `{}`", info.name),
                });
            };
            let a = if computed {
                let v = crate::core::eval(&self.e.g, &crate::core::Env::from(type_vals.clone()), &a);
                quote(&self.e.g, inner.len(), &self.e.reduce_type(&v))
            } else {
                (*a).clone()
            };
            type_vals.push(Val::var(inner.len()));
            // An argument holding types: closed, it is a value the types after
            // it are computed from; it is not passed to the solver.
            if let Tm::TyCon(id) | Tm::TyConApp(id, _) = self.zonk(inner.len(), &a) {
                if self.e.holds_types(id) {
                    let z = self.zonk(env.len(), arg);
                    let mut fv = std::collections::BTreeSet::new();
                    crate::core::free_vars(&z, 0, &mut fv);
                    if !fv.is_empty() {
                        return out("a type computed from a value the prover can't see");
                    }
                    let shown = crate::core::show(&self.e.g, &[], &z);
                    *type_vals.last_mut().unwrap() = crate::core::eval(&self.e.g, &crate::core::Env::new(), &z);
                    computed = true;
                    tys.push(Sort::Unin(format!("val#{shown}"), Vec::new()));
                    inner.push(Ent::Opaque(shown.clone()));
                    post_env.push(Ent::Opaque(shown));
                    t = (*b).clone();
                    k += 1;
                    continue;
                }
            }
            if self.is_kind(&a) {
                // A type constructor (M25): it picks the instance.
                let e = self.ty_fun(env, arg).ok_or_else(|| Outside("a type constructor the prover can't see".into()))?;
                let key = match &e {
                    Ent::TyFun(t, ps) => format!("tyfun#{t:?}{ps:?}"),
                    Ent::TyVar(n) => format!("tyvar#{n}"),
                    _ => unreachable!(),
                };
                self.ty_funs.insert(key.clone(), e.clone());
                tys.push(Sort::Unin(key, Vec::new()));
                inner.push(e.clone());
                post_env.push(e);
                t = (*b).clone();
                k += 1;
                continue;
            }
            if self.is_type(&a) {
                let s = self.sort_of(env, arg)?;
                tys.push(s.clone());
                inner.push(Ent::Ty(s.clone()));
                post_env.push(Ent::Ty(s));
            } else {
                let dict = self.is_dict_ty(&a);
                if dict || matches!(self.zonk(inner.len(), &a), Tm::Pi(..)) {
                    // A known function argument picks a specialized instance;
                    // any other is passed as a value (#630). So does a known
                    // dictionary (#615).
                    // At an opaque dictionary (below), a function is passed
                    // as a value, so that equal functions are equal.
                    let opaque = !dict && dpos.and_then(|p| inner.get(p)).is_some_and(|e| matches!(e, Ent::Term(_, Sort::Unin(..))));
                    // So does a function Z3 can't see into (sealed, or a
                    // builtin), where the argument can be a value (#231): a
                    // specialized symbol would be unrelated to the same call
                    // made with the function as a value, as inside a body
                    // where the lambda mentions the body's variables.
                    let as_value = if !dict && !opaque && !self.reflected(d) {
                        let want = self.sort_of(&inner, &a)?;
                        self.fun_value(env, arg, &want).ok().map(|fv| (fv, want))
                    } else {
                        None
                    };
                    if let Some((fv, want)) = as_value {
                        funs.push("*".into());
                        vals.push(fv.clone());
                        inner.push(Ent::Term(fv.clone(), want.clone()));
                        post_env.push(Ent::Term(fv, want));
                        t = (*b).clone();
                        k += 1;
                        continue;
                    }
                    let known = if opaque {
                        None
                    } else if dict {
                        match self.known_fun(env, arg) {
                            Some(k) => Some(k),
                            None => self.known_dict(env, arg)?,
                        }
                    } else {
                        self.known_fun(env, arg)
                    };
                    let Some(key) = known else {
                        let want = self.sort_of(&inner, &a)?;
                        let fv = if dict {
                            let (t, s) = self.term(env, arg)?;
                            self.expect(&s, &want)?;
                            t
                        } else {
                            self.fun_value(env, arg, &want)?
                        };
                        funs.push("*".into());
                        vals.push(fv.clone());
                        inner.push(Ent::Term(fv.clone(), want.clone()));
                        post_env.push(Ent::Term(fv, want));
                        t = (*b).clone();
                        k += 1;
                        continue;
                    };
                    funs.push(key.clone());
                    inner.push(Ent::Known(key.clone()));
                    post_env.push(Ent::Known(key));
                    t = (*b).clone();
                    k += 1;
                    continue;
                }
                let ps = self.sort_of(&inner, &a)?;
                let (at, s) = self.term(env, arg)?;
                self.expect(&s, &ps)?;
                vals.push(at.clone());
                inner.push(Ent::Term(at.clone(), ps.clone()));
                post_env.push(Ent::Term(at, ps));
            }
            t = (*b).clone();
            k += 1;
        }
        if k < args.len() {
            return out("a function returning a function");
        }
        if computed {
            let v = crate::core::eval(&self.e.g, &crate::core::Env::from(type_vals.clone()), &t);
            t = quote(&self.e.g, inner.len(), &self.e.reduce_type(&v));
        }
        let rs = self.sort_of(&inner, &t)?;
        // Builtins with a meaning in the solver.
        match qualified.as_str() {
            "std.bag.of" => {
                let elem = tys.first().cloned().unwrap_or(Sort::Int);
                let f = self.ensure_bag_of(&elem)?;
                return Ok((format!("({f} {})", vals.join(" ")), Sort::Bag(Box::new(elem))));
            }
            "std.bag.count" => return Ok((format!("(select {} {})", vals[1], vals[0]), Sort::Int)),
            "std.bag.sum" => {
                let elem = tys.first().cloned().unwrap_or(Sort::Int);
                return Ok((format!("((_ map (+ (Int Int) Int)) {} {})", vals[0], vals[1]), Sort::Bag(Box::new(elem))));
            }
            // A string is already its UTF-8 bytes.
            "std.utf8.encode" | "std.string.bytes" => return Ok((vals[0].clone(), Sort::Seq(Box::new(Sort::Int)))),
            // An array but its first element: the slice after it, as the
            // runtime's primitive makes it, so a sequence pattern's rest is
            // known (`x :: rest` on `b"ab" ++ post` leaves `b"b" ++ post`, #232).
            "std.prelude.array_rest" => {
                let xs = &vals[0];
                return Ok((format!("(seq.extract {xs} 1 (- (seq.len {xs}) 1))"), rs));
            }
            // `word` occurs in `src` at `i` (the Rust primitive, exactly).
            "std.bytes.matches_at" => {
                let (src, i, w) = (&vals[0], &vals[1], &vals[2]);
                return Ok((
                    format!("(and (<= (+ {i} (seq.len {w})) (seq.len {src})) (= (seq.extract {src} {i} (seq.len {w})) {w}))"),
                    Sort::Bool,
                ));
            }
            _ => {}
        }
        // A constant array of literals (a table): its length and each
        // element, as facts (#638).
        if args.is_empty() {
            if let Some(r) = self.array_table(d, &rs)? {
                return Ok(r);
            }
        }
        // A class's function of a known instance's dictionary is that
        // instance's function (#615).
        if self.e.class_methods.contains(&d) {
            if let Some(r) = self.member_app(env, d, args, &inner)? {
                let (app, _) = r;
                if self.gathers_posts() {
                    // A `Nat` result where the class's preconditions hold.
                    let spec = self.e.specs.get(&d);
                    let has_pre = spec.is_some_and(|s| s.preds.iter().any(|p| !p.is_post));
                    let nat = has_pre && self.is_nat_tm(&t);
                    let has_post = spec.is_some_and(|s| s.preds.iter().any(|p| p.is_post));
                    if (has_post || nat) && !self.post_gathered(&app) {
                        post_env.push(Ent::Term(app.clone(), rs.clone()));
                        self.gather_post(&app, PostUse { def: d, env: post_env, nat, parts: Vec::new() });
                    }
                }
                return Ok((app, rs));
            }
        }
        // At a dictionary Z3 can't see into (a class over a type
        // constructor, M25), a class's function is uninterpreted: one
        // function per dictionary and type arguments (#615 i).
        let opaque_dict = self.e.class_methods.contains(&d)
            && self.dict_pos(d).and_then(|p| inner.get(p)).is_some_and(|e| matches!(e, Ent::Term(_, Sort::Unin(..))));
        // Otherwise a class's function, and an instance's dictionary, are
        // inlined: reading a field of the dictionary.
        if !opaque_dict && (self.e.class_methods.contains(&d) || self.e.dict_defs.contains(&d)) {
            if let Some(mut body) = self.e.g.defs[d.0 as usize].body.clone() {
                for _ in 0..inner.len() {
                    match body {
                        Tm::Lam(_, _, _, b) => body = (*b).clone(),
                        _ => return out("a class's function that is not a function"),
                    }
                }
                let (app, s) = self.term(&inner, &body)?;
                self.expect(&s, &rs)?;
                if self.gathers_posts() {
                    let has_post = self.e.specs.get(&d).is_some_and(|s| s.preds.iter().any(|p| p.is_post));
                    // What the result's type says of it: a class's type's
                    // predicates (#176), of the result or of its parts.
                    let parts = if self.post_gathered(&app) { Vec::new() } else { self.part_terms(&post_env, &t, &app, &rs) };
                    if (has_post || !parts.is_empty()) && !self.post_gathered(&app) {
                        post_env.push(Ent::Term(app.clone(), rs.clone()));
                        self.gather_post(&app, PostUse { def: d, env: post_env, nat: false, parts });
                    }
                }
                return Ok((app, rs));
            }
        }
        let inst = Inst { def: d, tys: tys.clone(), funs: funs.clone() };
        let name = self.inst_name(&inst);
        if effect.is_none() && !self.insts.contains_key(&inst) && !self.funs.contains_key(&name) {
            if self.reflected(d) && !opaque_dict {
                self.insts.insert(inst.clone(), None);
                self.inst_queue.push(inst);
            } else {
                let mut arg_sorts = Vec::new();
                for e in &post_env {
                    if let Ent::Term(_, s) = e {
                        arg_sorts.push(s.render(self.e));
                    }
                }
                self.funs.insert(name.clone(), format!("(declare-fun {name} ({}) {})", arg_sorts.join(" "), rs.render(self.e)));
                if self.is_nat_tm(&t) {
                    self.nat_axiom(&name, &arg_sorts);
                }
            }
        }
        let app = match effect {
            Some(c) => {
                self.funs.entry(c.clone()).or_insert_with(|| format!("(declare-fun {c} () {})", rs.render(self.e)));
                c
            }
            None if vals.is_empty() => name,
            None => format!("({name} {})", vals.join(" ")),
        };
        if self.gathers_posts() {
            // At a call on program values the result is a `Nat` where the
            // callee's precondition holds (outside it, a reflected body such
            // as `n - 1` can be negative).
            let nat = self.is_nat_tm(&t);
            let spec = self.e.specs.get(&d);
            let has_pre = spec.is_some_and(|s| s.preds.iter().any(|p| !p.is_post));
            let has_post = spec.is_some_and(|s| s.preds.iter().any(|p| p.is_post));
            // In a body, the arguments are the parameters' terms: a `Nat`
            // result is so where they are of the callee's types, like a
            // postcondition.
            let in_body = self.in_def;
            if nat && !has_pre && !in_body {
                let a = app.clone();
                self.nat_fact(&a);
            }
            let nat = nat && (has_pre || in_body);
            let mut parts = Vec::new();
            if !self.post_gathered(&app) {
                // The result's type at these arguments: a type argument
                // may be refined too (`Pair Bool (s~Nat, s > 3)` for `Pair a b`).
                let at = if computed { None } else { self.result_type_at(env.len(), &info_ty, args) };
                parts = match at {
                    Some(rt) => self.part_terms(env, &rt, &app, &rs),
                    None => self.part_terms(&post_env, &t, &app, &rs),
                };
            }
            if (has_post || nat || !parts.is_empty()) && !self.post_gathered(&app) {
                post_env.push(Ent::Term(app.clone(), rs.clone()));
                self.gather_post(&app, PostUse { def: d, env: post_env, nat, parts });
            }
        }
        Ok((app, rs))
    }

    /// `bag.of` on lists of `elem` (#553, #625).
    fn ensure_bag_of(&mut self, elem: &Sort) -> Tx<String> {
        let es = elem.render(self.e);
        let name = if *elem == Sort::Int { "|bag.of|".to_string() } else { sym(&format!("bag.of<{es}>")) };
        if self.funs.contains_key(&name) {
            return Ok(name);
        }
        let e = self.e;
        let wk = &e.g.well_known;
        let (Some(list), Some(cons)) = (wk.list, wk.cons) else { return out("no lists") };
        if let std::collections::btree_map::Entry::Vacant(v) = self.datatypes.entry(list) {
            v.insert(1);
            self.datatype_decl(list)?;
        }
        let def = format!(
            "(define-fun-rec {name} ((xs ({l} {es}))) (Array {es} Int) (ite ({c} xs) (let ((b ({name} ({t} xs))) (h ({hd} xs))) (store b h (+ (select b h) 1))) ((as const (Array {es} Int)) 0)))",
            l = ty_sym(self.e, list),
            c = tester(self.e, cons),
            t = sel_sym(self.e, cons, 1),
            hd = sel_sym(self.e, cons, 0),
        );
        self.funs.insert(name.clone(), def);
        Ok(name)
    }

    fn prim(&mut self, env: &[Ent], p: &Prim, args: &[Tm]) -> Tx<(String, Sort)> {
        let mut ts = Vec::new();
        let n = if matches!(p, Prim::Sub | Prim::Index) { 2 } else { args.len() };
        for a in &args[..n.min(args.len())] {
            ts.push(self.term(env, a)?);
        }
        let bin = |op: &str, ts: &[(String, Sort)], s: Sort| Ok((format!("({op} {} {})", ts[0].0, ts[1].0), s));
        // An operator the type checker rejected (`<` on a record) keeps
        // its operands (§7.3): their sorts say so.
        let list = self.wk().list;
        let is_list = |s: &Sort| matches!(s, Sort::Data(id, _) if Some(*id) == list);
        match p {
            Prim::Add | Prim::Sub | Prim::Mul | Prim::Div | Prim::Rem | Prim::Neg | Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge => {
                for (_, s) in &ts {
                    self.expect(s, &Sort::Int)?;
                }
            }
            Prim::Eq | Prim::Ne | Prim::Concat => self.expect(&ts[1].1, &ts[0].1)?,
            Prim::Index => self.expect(&ts[1].1, &Sort::Int)?,
            _ => {}
        }
        match p {
            Prim::Add => bin("+", &ts, Sort::Int),
            Prim::Sub => bin("-", &ts, Sort::Int),
            Prim::Mul => bin("*", &ts, Sort::Int),
            Prim::Div => bin("div", &ts, Sort::Int),
            Prim::Rem => bin("mod", &ts, Sort::Int),
            Prim::Neg => Ok((format!("(- {})", ts[0].0), Sort::Int)),
            Prim::Lt => bin("<", &ts, Sort::Bool),
            Prim::Le => bin("<=", &ts, Sort::Bool),
            Prim::Gt => bin(">", &ts, Sort::Bool),
            Prim::Ge => bin(">=", &ts, Sort::Bool),
            Prim::Eq => bin("=", &ts, Sort::Bool),
            Prim::Ne => Ok((format!("(not (= {} {}))", ts[0].0, ts[1].0), Sort::Bool)),
            Prim::Concat => match &ts[0].1 {
                s @ (Sort::Str | Sort::Seq(_)) => {
                    let s = s.clone();
                    let t = format!("(seq.++ {} {})", ts[0].0, ts[1].0);
                    if !self.in_def {
                        self.concats.insert(t.clone(), (ts[0].0.clone(), ts[1].0.clone()));
                    }
                    Ok((t, s))
                }
                s if is_list(s) => {
                    let s = s.clone();
                    let f = self.list_fun("append", &s, 2, s.clone())?;
                    Ok((format!("({f} {} {})", ts[0].0, ts[1].0), s))
                }
                // Only strings, arrays and lists have `++`.
                _ => Err(self.ill_sorted()),
            },
            Prim::Len => match &ts[0].1 {
                Sort::Seq(_) => Ok((format!("(seq.len {})", ts[0].0), Sort::Int)),
                Sort::Str => Ok((format!("(seq.len {})", ts[0].0), Sort::Int)),
                s if is_list(s) => {
                    let s = s.clone();
                    let f = self.list_fun("len", &s, 1, Sort::Int)?;
                    let ls = s.render(self.e);
                    self.nat_axiom(&f, &[ls]);
                    let t = format!("({f} {})", ts[0].0);
                    self.nat_fact(&t);
                    Ok((t, Sort::Int))
                }
                // Only strings, arrays and lists have `len`.
                _ => Err(self.ill_sorted()),
            },
            Prim::Index => {
                let elem = match &ts[0].1 {
                    Sort::Seq(e) => (**e).clone(),
                    Sort::Str => Sort::Int,
                    _ => return Err(self.ill_sorted()),
                };
                let t = format!("(seq.nth {} {})", ts[0].0, ts[1].0);
                // An element has its type's refinement (#624): a `U8` of
                // `Bytes` is `>= 0` and `< 256`.
                if !self.in_def && self.fact_seen.insert(t.clone()) {
                    self.index_concat(&ts[0].0, &ts[1].0);
                    if let Some(ety) = args.get(2) {
                        let facts = self.value_terms(env, ety, &t, &elem);
                        self.asserts.extend(facts);
                    }
                    if let Sort::Data(id, _) = &elem {
                        self.real_values.push((t.clone(), *id));
                    }
                }
                Ok((t, elem))
            }
            Prim::Par => Ok(ts[0].clone()),
            Prim::When => out("a `when`"),
            Prim::Builtin(n) => out(match self.e.hidden_home(&self.user, n) {
                Some(home) => format!("a private function built into `{home}`"),
                None => format!("the builtin `{n}`"),
            }),
            Prim::Forall => out("a `forall`"),
            Prim::Effect(_) => out("a call with effects"),
        }
    }

    /// `++` and `len` on lists, as recursive functions.
    fn list_fun(&mut self, what: &str, list: &Sort, _arity: usize, _res: Sort) -> Tx<String> {
        let e = self.e;
        let wk = &e.g.well_known;
        let (Some(cons), Some(nil)) = (wk.cons, wk.nil) else { return out("no lists") };
        let ls = list.render(self.e);
        let name = sym(&format!("list.{what}<{ls}>"));
        if self.funs.contains_key(&name) {
            return Ok(name);
        }
        let is_cons = tester(self.e, cons);
        let hd = sel_sym(self.e, cons, 0);
        let tl = sel_sym(self.e, cons, 1);
        let def = match what {
            "len" => format!("(define-fun-rec {name} ((xs {ls})) Int (ite ({is_cons} xs) (+ 1 ({name} ({tl} xs))) 0))"),
            _ => format!(
                "(define-fun-rec {name} ((xs {ls}) (ys {ls})) {ls} (ite ({is_cons} xs) ((as {c} {ls}) ({hd} xs) ({name} ({tl} xs) ys)) ys))",
                c = con_sym(self.e, cons)
            ),
        };
        let _ = nil;
        self.funs.insert(name.clone(), def);
        Ok(name)
    }

    fn case(&mut self, env: &[Ent], s: &Tm, c: &CaseTm) -> Tx<(String, Sort)> {
        let (st, ss) = self.term(env, s)?;
        let x = st.clone();
        let mut arms: Vec<(Option<String>, String, Sort)> = Vec::new();
        match &ss {
            Sort::Bool => {
                for (con, _, body) in &c.branches {
                    if matches!(body, Tm::Error) {
                        continue;
                    }
                    let (bt, bs) = self.term(env, body)?;
                    let cond = if Some(*con) == self.wk().true_con { x.clone() } else { format!("(not {x})") };
                    arms.push((Some(cond), bt, bs));
                }
            }
            Sort::Data(id, sargs) => {
                self.tested.insert(ss.clone());
                let senv = self.sort_env(*id, sargs);
                for (con, n, body) in &c.branches {
                    if matches!(body, Tm::Error) {
                        continue;
                    }
                    if self.e.g.cons[con.0 as usize].ty != *id {
                        return Err(self.ill_sorted());
                    }
                    let fs = self.con_fields(*con, &senv)?;
                    let mut env2 = env.to_vec();
                    for k in 0..*n {
                        match fs.iter().find(|(i, _)| *i == k) {
                            Some((_, fsort)) => env2.push(Ent::Term(format!("({} {x})", sel_sym(self.e, *con, k)), fsort.clone())),
                            None => {
                                let s = self.type_field_sort(*con, k, &senv);
                                env2.push(Ent::Ty(s));
                            }
                        }
                    }
                    let (bt, bs) = self.term(&env2, body)?;
                    arms.push((Some(format!("({} {x})", tester(self.e, *con))), bt, bs));
                }
            }
            // A string's one constructor holds its bytes, which it is (#170).
            Sort::Str => {
                for (_, n, body) in &c.branches {
                    if matches!(body, Tm::Error) {
                        continue;
                    }
                    let mut env2 = env.to_vec();
                    env2.extend((0..*n).map(|_| Ent::Term(x.clone(), Sort::Seq(Box::new(Sort::Int)))));
                    let (bt, bs) = self.term(&env2, body)?;
                    arms.push((None, bt, bs));
                }
            }
            Sort::Tuple(_) => {
                // A tuple has one constructor.
                if let Some((_, _, body)) = c.branches.first() {
                    let (bt, bs) = self.term(env, body)?;
                    arms.push((None, bt, bs));
                }
            }
            _ => {}
        }
        for (l, body) in &c.lits {
            if matches!(body, Tm::Error) {
                continue;
            }
            let (lt, ls) = match l {
                Lit::Num(n) => (smt_int(*n), Sort::Int),
                Lit::Big(n) => (smt_int((**n).clone()), Sort::Int),
                Lit::Str(s) => (smt_bytes(s.as_bytes()), Sort::Str),
                Lit::Bytes(b) => (smt_bytes(b), Sort::Seq(Box::new(Sort::Int))),
            };
            self.expect(&ss, &ls)?;
            let (bt, bs) = self.term(env, body)?;
            arms.push((Some(format!("(= {x} {lt})")), bt, bs));
        }
        if let Some(d) = c.default.as_ref().filter(|d| !matches!(d, Tm::Error)) {
            let (bt, bs) = self.term(env, d)?;
            arms.push((None, bt, bs));
        }
        let Some((_, last, sort)) = arms.pop() else { return out("a `match` with no reachable arm") };
        for (_, _, s) in &arms {
            self.expect(s, &sort)?;
        }
        let mut acc = last;
        while let Some((cond, bt, _)) = arms.pop() {
            acc = match cond {
                Some(c) => format!("(ite {c} {bt} {acc})"),
                None => bt,
            };
        }
        Ok((acc, sort))
    }

    // ── reflected definitions and postconditions ────────────────────────────

    /// The definitions: all reflected; all uninterpreted; and the parts to
    /// reflect some only (`focus`).
    fn define_instances(&mut self) -> (Vec<String>, Vec<String>, Focus) {
        while let Some(inst) = self.inst_queue.pop() {
            let r = self.define_shared(&inst);
            // A `Nat` result is non-negative, for every argument.
            let mut ty = self.e.g.defs[inst.def.0 as usize].ty.clone();
            while let Tm::Pi(_, _, _, _, b) = ty {
                ty = (*b).clone();
            }
            // Z3 applies the definition to values no program can build
            // (`Option Nat` is `Option Int` to it; invariants and
            // preconditions aren't in sorts), where a `Nat` body can be
            // negative. So "the result is >= 0 for every argument" is stated
            // only when it holds for every solver value (`nonneg_fn`).
            if self.is_nat_tm(&ty) && self.nonneg_fn(inst.def, &mut Vec::new()) {
                if let Ok((_, params, _)) = self.inst_sig(&inst) {
                    let name = self.inst_name(&inst);
                    let sorts: Vec<String> = params.iter().map(|(_, s)| s.render(self.e)).collect();
                    self.nat_axiom(&name, &sorts);
                }
            }
            self.insts.insert(inst, r.ok());
        }
        let mut decls = Vec::new();
        let mut opaque = Vec::new();
        let mut group = Vec::new();
        let all: Vec<(Inst, Option<Defn>)> = self.insts.iter().map(|(a, b)| (a.clone(), b.clone())).collect();
        // Instances at types of one sort (`String` and `Bytes` are both
        // `(Seq Int)`, §7.3) have one SMT name: each name is defined, or
        // else declared, once.
        let defined: HashSet<String> = all.iter().filter_map(|(_, d)| d.as_ref().map(|(n, _, _)| n.clone())).collect();
        let mut seen = HashSet::new();
        for (inst, def) in &all {
            let name = match def {
                Some((n, _, _)) => n.clone(),
                None => self.inst_name(inst),
            };
            if (def.is_none() && defined.contains(&name)) || !seen.insert(name) {
                continue;
            }
            match def {
                Some((name, head, body)) => {
                    let d = self.uninterp_decl(inst);
                    if let Some(d) = &d {
                        opaque.push(d.clone());
                    }
                    group.push((name.clone(), head.clone(), body.clone(), d));
                }
                None => {
                    // Not translatable: uninterpreted.
                    if let Some(d) = self.uninterp_decl(inst) {
                        decls.push(d);
                    }
                }
            }
        }
        let reflected = !group.is_empty();
        let mut copies = String::new();
        if reflected {
            let parts: Vec<(&str, &str, &str)> = group.iter().map(|g| (g.0.as_str(), g.1.as_str(), g.2.as_str())).collect();
            let (c, bodies) = definitions(&parts, self.defs.map(|d| &d.1));
            copies = c;
            for (g, (h, b)) in group.iter_mut().zip(bodies) {
                g.1 = h;
                g.2 = b;
            }
            let heads: Vec<&str> = group.iter().map(|g| g.1.as_str()).collect();
            let bodies: Vec<&str> = group.iter().map(|g| g.2.as_str()).collect();
            decls.push(format!("{copies}(define-funs-rec ({}) ({}))", heads.join(" "), bodies.join(" ")));
        }
        // The uninterpreted variant shares the rest (`decls` minus the group).
        let mut only = decls.clone();
        if reflected {
            only.pop();
        }
        let focus = Focus { others: only.clone(), copies, group };
        if reflected {
            only.extend(opaque);
        }
        (decls, only, focus)
    }

    fn inst_name(&self, inst: &Inst) -> String {
        if let Some(n) = self.defs.and_then(|d| d.2.borrow().names.get(inst).cloned()) {
            return n;
        }
        let n = self.inst_name_of(inst);
        if let Some(d) = self.defs {
            d.2.borrow_mut().names.insert(inst.clone(), n.clone());
        }
        n
    }

    fn inst_name_of(&self, inst: &Inst) -> String {
        let info = &self.e.g.defs[inst.def.0 as usize];
        let mut q = format!("{}.{}", info.module, info.name);
        if !inst.tys.is_empty() {
            q += &format!("<{}>", inst.tys.iter().map(|s| s.render(self.e)).collect::<Vec<_>>().join(","));
        }
        if !inst.funs.is_empty() {
            q += &format!("[{}]", inst.funs.join(","));
        }
        sym(&q)
    }

    /// If `arg` (under `env`) is a known function value, its key.
    /// A dictionary built by an instance from types of the obligation and
    /// known dictionaries (`Functor (Pair k)` with `k` a type parameter,
    /// M25): known, its arguments kept by its key.
    fn known_dict(&mut self, env: &[Ent], arg: &Tm) -> Tx<Option<String>> {
        let arg = self.zonk(env.len(), arg);
        let (h, dargs) = arg.spine_cloned();
        let Tm::Def(dd) = h else { return Ok(None) };
        if !self.e.dict_defs.contains(dd) {
            return Ok(None);
        }
        let mut dty = self.e.g.defs[dd.0 as usize].ty.clone();
        let mut ents = Vec::new();
        let mut parts = Vec::new();
        for a in &dargs {
            let Tm::Pi(_, _, _, dom, cod) = dty else { return Ok(None) };
            if self.is_kind(&dom) {
                let Some(e) = self.ty_fun(env, a) else { return Ok(None) };
                parts.push(match &e {
                    Ent::TyFun(t, ps) => format!("{t:?}{}", ps.iter().map(|p| p.render(self.e)).collect::<Vec<_>>().join(",")),
                    Ent::TyVar(n) => n.clone(),
                    _ => return Ok(None),
                });
                ents.push(e);
            } else if self.is_type(&dom) {
                let s = self.sort_of(env, a)?;
                parts.push(s.render(self.e));
                ents.push(Ent::Ty(s));
            } else if self.is_dict_ty(&dom) {
                let k = match self.known_fun(env, a) {
                    Some(k) => k,
                    None => match self.known_dict(env, a)? {
                        Some(k) => k,
                        None => return Ok(None),
                    },
                };
                parts.push(k.clone());
                ents.push(Ent::Known(k));
            } else {
                return Ok(None);
            }
            dty = (*cod).clone();
        }
        let info = &self.e.g.defs[dd.0 as usize];
        let key = format!("dict#{}.{}[{}]", info.module, info.name, parts.join(";"));
        self.known.insert(key.clone(), arg);
        self.dict_args.insert(key.clone(), ents);
        Ok(Some(key))
    }

    fn known_fun(&mut self, env: &[Ent], arg: &Tm) -> Option<String> {
        let arg = self.zonk(env.len(), arg);
        if let Tm::Var(i) = &arg {
            return match self.resolve(env, *i).ok()? {
                Ent::Known(k) => Some(k),
                _ => None,
            };
        }
        if !closed(&arg, 0) {
            return None;
        }
        // One normal form, so the same function written in two places (say, a
        // lambda in a body and in a lemma, one with its pattern `let`s still
        // there) is one key.
        let arg = if matches!(arg, Tm::Def(_)) { arg } else { quote(&self.e.g, 0, &eval(&self.e.g, &crate::core::Env::new(), &arg)) };
        let h = arg.head();
        let key = match h {
            Tm::Def(d) if matches!(arg, Tm::Def(_)) => {
                let info = &self.e.g.defs[d.0 as usize];
                format!("{}.{}", info.module, info.name)
            }
            _ => {
                use std::hash::{Hash, Hasher};
                let mut hs = std::collections::hash_map::DefaultHasher::new();
                // Binder names don't matter: `\x -> …` written twice is one function.
                let mut text = format!("{arg:?}");
                for binder in ["Lam(\"", "Pi(\"", "Let(\""] {
                    let mut out_ = String::new();
                    let mut rest = text.as_str();
                    while let Some(k) = rest.find(binder) {
                        out_ += &rest[..k + binder.len()];
                        rest = &rest[k + binder.len()..];
                        if let Some(e) = rest.find('"') {
                            rest = &rest[e..];
                        }
                    }
                    out_ += rest;
                    text = out_;
                }
                text.hash(&mut hs);
                if std::env::var_os("CHECKERS_KNOWN_DUMP").is_some() {
                    eprintln!("KNOWN {:08x} {arg:?}", hs.clone().finish() as u32);
                }
                format!("fn#{:08x}", hs.finish() as u32)
            }
        };
        self.known.insert(key.clone(), arg);
        Some(key)
    }

    /// Apply a closed function term to arguments under `env`.
    fn apply_known(&mut self, env: &[Ent], f: &Tm, args: &[(Tm, Mult)]) -> Tx<(String, Sort)> {
        match f {
            Tm::Lam(..) => {
                // The body sees only its parameters (the lambda is closed).
                let mut inner = Vec::new();
                let mut body = f;
                let mut taken = 0;
                for (a, m) in args {
                    if *m == Mult::Zero {
                        // A type argument (M25).
                        let e = match self.ty_fun(env, a) {
                            Some(e) => e,
                            None => Ent::Ty(self.sort_of(env, a)?),
                        };
                        inner.push(e);
                    } else if let Tm::Var(i) = a {
                        // A known function stays known.
                        let e = self.resolve(env, *i)?;
                        inner.push(e);
                    } else {
                        let (at, s) = self.term(env, a)?;
                        inner.push(Ent::Term(at, s));
                    }
                    if let Tm::Lam(_, _, _, b) = body {
                        if taken == inner.len() - 1 {
                            body = b;
                            taken += 1;
                        }
                    }
                }
                if matches!(body, Tm::Lam(..)) {
                    return out("a partially applied lambda");
                }
                // A lambda returning a function (a dictionary's polymorphic
                // field, M25): apply what it returns to the other arguments.
                let n = inner.len();
                let mut body = crate::stage::shift(body, n - taken, 0);
                for (j, (_, m)) in args.iter().enumerate().skip(taken) {
                    let i = if *m == Mult::Zero { crate::core::Icit::Impl } else { crate::core::Icit::Expl };
                    body = Tm::App(Rc::new(body), Rc::new(Tm::Var(n - 1 - j)), i, *m, crate::core::Pos::NONE);
                }
                self.term(&inner, &body)
            }
            _ => {
                // Re-express the arguments as variables of a fresh environment.
                let mut inner = Vec::new();
                let mut tms = Vec::new();
                let n = args.len();
                for (k, (a, m)) in args.iter().enumerate() {
                    let ent = match self.known_fun(env, a) {
                        Some(key) => Ent::Known(key),
                        None => match self.term(env, a) {
                            Ok((t, s)) => Ent::Term(t, s),
                            Err(e) => match self.sort_of(env, a) {
                                Ok(s) => Ent::Ty(s),
                                Err(_) => return Err(e),
                            },
                        },
                    };
                    inner.push(ent);
                    tms.push((Tm::Var(n - 1 - k), *m));
                }
                let mut app = f.clone();
                for (t, m) in tms {
                    app = Tm::App(Rc::new(app), Rc::new(t), crate::core::Icit::Expl, m, crate::core::Pos::NONE);
                }
                self.term(&inner, &app)
            }
        }
    }

    fn inst_sig(&mut self, inst: &Inst) -> Tx<InstSig> {
        let ty = self.e.g.defs[inst.def.0 as usize].ty.clone();
        let mut env = Vec::new();
        let mut params = Vec::new();
        let mut t = ty;
        let mut tk = 0;
        let mut fk = 0;
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = t.clone() {
            if self.is_kind(&a) {
                let e = match inst.tys.get(tk) {
                    Some(Sort::Unin(key, _)) => self.ty_funs.get(key).cloned(),
                    _ => None,
                };
                env.push(e.ok_or_else(|| Outside("a type constructor".into()))?);
                tk += 1;
            } else if self.is_type(&a) {
                env.push(Ent::Ty(inst.tys.get(tk).cloned().unwrap_or(Sort::Int)));
                tk += 1;
            } else if self.is_dict_ty(&a) || matches!(self.zonk(env.len(), &a), Tm::Pi(..)) {
                let key = inst.funs.get(fk).cloned().ok_or_else(|| Outside("a function parameter".into()))?;
                fk += 1;
                if key == "*" {
                    let s = self.sort_of(&env, &a)?;
                    let n = format!("p{k}");
                    params.push((n.clone(), s.clone()));
                    env.push(Ent::Term(n, s));
                } else {
                    env.push(Ent::Known(key));
                }
            } else {
                let s = self.sort_of(&env, &a)?;
                let n = format!("p{k}");
                params.push((n.clone(), s.clone()));
                env.push(Ent::Term(n, s));
            }
            t = (*b).clone();
            k += 1;
        }
        let r = self.sort_of(&env, &t)?;
        Ok((env, params, r))
    }

    /// An instance's declaration, uninterpreted. Its sorts are those of its
    /// definition, declared already.
    fn uninterp_decl(&mut self, inst: &Inst) -> Option<String> {
        if let Some(d) = self.defs.and_then(|d| d.2.borrow().uninterp.get(inst).cloned()) {
            return d;
        }
        let d = self.uninterp_decl_of(inst);
        if let Some(defs) = self.defs {
            defs.2.borrow_mut().uninterp.insert(inst.clone(), d.clone());
        }
        d
    }

    fn uninterp_decl_of(&mut self, inst: &Inst) -> Option<String> {
        let name = self.inst_name(inst);
        let (_, params, r) = self.inst_sig(inst).ok()?;
        Some(format!(
            "(declare-fun {name} ({}) {})",
            params.iter().map(|(_, s)| s.render(self.e)).collect::<Vec<_>>().join(" "),
            r.render(self.e)
        ))
    }

    fn define(&mut self, inst: &Inst) -> Tx<Defn> {
        let name = self.inst_name(inst);
        let (env, params, r) = self.inst_sig(inst)?;
        let mut body = self.e.g.defs[inst.def.0 as usize].body.clone().ok_or_else(|| Outside("no body".into()))?;
        for _ in 0..env.len() {
            match body {
                Tm::Lam(_, _, _, b) => body = (*b).clone(),
                _ => return out("a body that is not a function"),
            }
        }
        let saved = self.in_def;
        self.in_def = true;
        let saved_posts = std::mem::replace(&mut self.body_posts, self.bodies.then(|| (Vec::new(), HashSet::new())));
        let r_body = self.term(&env, &body);
        let guard = self.domain(inst, &env);
        let posts = std::mem::replace(&mut self.body_posts, saved_posts).map(|p| p.0).unwrap_or_default();
        self.in_def = saved;
        let (mut bt, bs) = r_body?;
        self.expect(&bs, &r)?;
        // A definition recursing by `decreasing` ends only where its
        // precondition holds and its `Nat`s are `Nat`s: Z3 gets the equation
        // there, and an unknown value elsewhere (M17).
        if let Some(guard) = guard? {
            let out_name = format!("|{}#outside|", name.trim_matches('|'));
            self.funs.insert(
                out_name.clone(),
                format!(
                    "(declare-fun {out_name} ({}) {})",
                    params.iter().map(|(_, s)| s.render(self.e)).collect::<Vec<_>>().join(" "),
                    r.render(self.e)
                ),
            );
            let args: Vec<&str> = params.iter().map(|(n, _)| n.as_str()).collect();
            let outside = if args.is_empty() { out_name } else { format!("({out_name} {})", args.join(" ")) };
            bt = format!("(ite {guard} {bt} {outside})");
        }
        let head = format!(
            "({name} ({}) {})",
            params.iter().map(|(n, s)| format!("({n} {})", s.render(self.e))).collect::<Vec<_>>().join(" "),
            r.render(self.e)
        );
        self.body_post_axioms(inst.def, &name, &params, posts);
        Ok((name, head, bt))
    }

    /// Where a definition recursing by `decreasing` is known to end: its
    /// preconditions, and its `Nat` parameters non-negative. None for other
    /// definitions (structural recursion ends on every value Z3 can build).
    fn domain(&mut self, inst: &Inst, env: &[Ent]) -> Tx<Option<String>> {
        let Some(spec) = self.e.specs.get(&inst.def).cloned() else { return Ok(None) };
        // A measure written, or guessed (#641).
        if spec.measure.is_none() && !self.e.guessed.contains(&inst.def) {
            return Ok(None);
        }
        // Its recursion ends without the preconditions: only `Nat`s matter.
        let everywhere = self.e.ends_everywhere.lock().unwrap_or_else(|e| e.into_inner()).contains(&inst.def);
        let mut conds = Vec::new();
        // Nat parameters.
        let mut ty = self.e.g.defs[inst.def.0 as usize].ty.clone();
        let mut k = 0;
        while let Tm::Pi(_, _, _, a, b) = ty {
            if self.is_nat_tm(&a) {
                if let Some(Ent::Term(n, _)) = env.get(k) {
                    conds.push(format!("(>= {n} 0)"));
                }
            }
            ty = (*b).clone();
            k += 1;
        }
        // Preconditions, elaborated with the result in scope after the parameters.
        let mut penv = env.to_vec();
        penv.push(Ent::Opaque("the result".into()));
        // A `forall` (#632) is proved at each call; termination doesn't rest on it.
        for pred in spec.preds.iter().filter(|p| !p.is_post && !everywhere && !has_forall(&p.tm)) {
            conds.push(self.prop(&penv, &pred.tm)?);
        }
        Ok(match conds.len() {
            0 => None,
            1 => conds.pop(),
            _ => Some(format!("(and {})", conds.join(" "))),
        })
    }

    /// Calls' postconditions are gathered here: in the query's goal and
    /// facts, or in the reflected body being translated (`body_posts`),
    /// outside a lambda, whose variables aren't the body's parameters.
    fn gathers_posts(&self) -> bool {
        !self.in_def || (self.body_posts.is_some() && self.lam_depth == 0)
    }

    /// The postcondition of the call `app` is gathered already.
    fn post_gathered(&self, app: &str) -> bool {
        match &self.body_posts {
            Some((_, seen)) if self.in_def => seen.contains(app),
            _ => self.post_seen.contains(app),
        }
    }

    /// Gather the postcondition of the call `app`.
    fn gather_post(&mut self, app: &str, p: PostUse) {
        match &mut self.body_posts {
            Some((posts, seen)) if self.in_def => {
                if seen.insert(app.to_string()) {
                    posts.push(p);
                }
            }
            _ => {
                if self.post_seen.insert(app.to_string()) {
                    self.posts.push(p);
                }
            }
        }
    }

    /// The postconditions of the calls in the reflected body of `name`, as
    /// axioms over its parameters, used where `name` is applied (#343): Z3
    /// unfolds the body there. Each holds where the callee's preconditions
    /// do, and its arguments are of its parameters' types (a `Nat` is
    /// non-negative, a refinement's predicates hold): so for every argument
    /// Z3 tries, whether the body reaches the call or not. A definition
    /// without parameters (a constant) has one body, unfolded wherever it is
    /// named: its calls' postconditions are facts, with no quantifier.
    fn body_post_axioms(&mut self, def: DefId, name: &str, params: &[(String, Sort)], posts: Vec<PostUse>) {
        let binds: Vec<String> = params.iter().map(|(n, s)| format!("({n} {})", s.render(self.e))).collect();
        let app = format!("({name} {})", params.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(" "));
        // The callee's conditions are translated as a body's are: calls in
        // them add nothing more.
        let saved = std::mem::replace(&mut self.in_def, true);
        for (k, p) in posts.into_iter().enumerate() {
            // A call of the function itself, or of one calling it back,
            // would make a term the axiom applies to again, without end.
            if p.def == def || self.reaches(p.def, def) {
                continue;
            }
            let spec = self.e.specs.get(&p.def).cloned().unwrap_or_default();
            let mut pres = self.arg_domains(&p);
            let mut ok = true;
            for pred in spec.preds.iter().filter(|x| !x.is_post && !has_forall(&x.tm)) {
                match self.prop(&p.env, &pred.tm) {
                    Ok(t) => pres.push(t),
                    Err(_) => ok = false,
                }
            }
            if !ok {
                continue;
            }
            let mut goals = Vec::new();
            if p.nat {
                if let Some(Ent::Term(r, _)) = p.env.last() {
                    goals.push(format!("(>= {r} 0)"));
                }
            }
            for pred in spec.preds.iter().filter(|x| x.is_post) {
                if let Ok(t) = self.prop(&p.env, &pred.tm) {
                    goals.push(t);
                }
            }
            goals.extend(p.parts);
            dedup(&mut pres);
            dedup(&mut goals);
            if goals.is_empty() {
                continue;
            }
            let goal = if goals.len() == 1 { goals.pop().unwrap_or_default() } else { format!("(and {})", goals.join(" ")) };
            let body = implies(&pres, goal);
            let axiom = if params.is_empty() { body } else { format!("(forall ({}) (! {body} :pattern ({app})))", binds.join(" ")) };
            self.body_axioms.insert(format!("{}#post{k}", name.trim_matches('|')), axiom);
        }
        self.in_def = saved;
    }

    /// `from`'s body applies `to`, through any number of definitions' bodies.
    fn reaches(&mut self, from: DefId, to: DefId) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![from];
        while let Some(d) = stack.pop() {
            if !seen.insert(d) {
                continue;
            }
            let refs = self.def_refs.entry(d).or_insert_with(|| {
                let mut out = Vec::new();
                if let Some(b) = &self.e.g.defs[d.0 as usize].body {
                    def_refs(b, &mut out);
                }
                out
            });
            if refs.contains(&to) {
                return true;
            }
            stack.extend(refs.iter().copied());
        }
        false
    }

    /// What a call's arguments satisfy, being of the callee's parameters'
    /// types: a `Nat` is non-negative, a refinement's predicates hold.
    fn arg_domains(&mut self, p: &PostUse) -> Vec<String> {
        let mut out = Vec::new();
        let mut ty = self.e.g.defs[p.def.0 as usize].ty.clone();
        let mut k = 0;
        while let Tm::Pi(_, m, _, dom, cod) = ty {
            if let (Mult::One | Mult::Many, Some(Ent::Term(a, s))) = (m, p.env.get(k)) {
                if !self.is_dict_ty(&dom) && !matches!(*dom, Tm::Pi(..)) {
                    let (a, s) = (a.clone(), s.clone());
                    out.extend(self.domain_terms(&p.env[..k], &dom, &a, &s));
                }
            }
            ty = (*cod).clone();
            k += 1;
        }
        out
    }

    fn assume_posts(&mut self) {
        let mut rounds = 0;
        while !self.posts.is_empty() && rounds < 3 {
            rounds += 1;
            let posts = std::mem::take(&mut self.posts);
            for p in posts {
                let spec = self.e.specs.get(&p.def).cloned().unwrap_or_default();
                // The postcondition holds where the precondition does.
                let mut pres = Vec::new();
                let mut ok = true;
                // A `forall` precondition is proved at the call (#632), and
                // Z3 can't use it in a guard without instantiating it.
                for pred in spec.preds.iter().filter(|x| !x.is_post && !has_forall(&x.tm)) {
                    match self.prop(&p.env, &pred.tm) {
                        Ok(t) => pres.push(t),
                        Err(_) => ok = false,
                    }
                }
                if !ok {
                    continue;
                }
                let mut goals = Vec::new();
                if p.nat {
                    if let Some(Ent::Term(r, _)) = p.env.last() {
                        goals.push(format!("(>= {r} 0)"));
                    }
                }
                for pred in spec.preds.iter().filter(|x| x.is_post) {
                    if let Ok(t) = self.prop(&p.env, &pred.tm) {
                        goals.push(t);
                    }
                }
                goals.extend(p.parts);
                for t in goals {
                    self.asserts.push(implies(&pres, t));
                }
            }
        }
    }

    /// The full query for an obligation: facts, and the negated goal.
    pub fn query(mut self, ob: &Obligation) -> Tx<Query> {
        self.ctx = vec![None; ob.ctx.len()];
        self.ctx_src = ob.ctx.clone();
        self.reps = ob.reps.clone();
        let lvl = ob.ctx.len();
        let goal_tm = quote(&self.e.g, lvl, &ob.goal);
        let mut facts = Vec::new();
        // Proving a `forall` (#632): its body, at fresh values; a `forall`
        // in scope over the same types is given at those values (how a
        // function passes its own hypothesis on).
        let (goal, gs) = match &goal_tm {
            Tm::PrimApp(Prim::Forall, a) if a.len() == 1 => {
                let sorts = self.forall_sorts(lvl, &a[0])?;
                let names: Vec<String> = (0..sorts.len()).map(|k| format!("|forall.{k}|")).collect();
                let mut shown_names = Vec::new();
                let mut pt = &a[0];
                while let Tm::Pi(x, _, _, _, b) = pt {
                    shown_names.push(x.to_string());
                    pt = b;
                }
                for (k, (n, s)) in names.iter().zip(&sorts).enumerate() {
                    self.consts.push(format!("(declare-const {n} {})", s.render(self.e)));
                    if let Some(x) = shown_names.get(k) {
                        self.shown.push((n.clone(), x.clone()));
                        if *s == Sort::Str {
                            self.string_vars.push(n.clone());
                        }
                    }
                }
                let (g, domain) = self.forall_body_at(lvl, &a[0], &names, &sorts)?.ok_or_else(|| Outside("a `forall`".into()))?;
                // The fresh values are in the variables' types.
                facts.extend(domain);
                for f in &ob.facts {
                    if let Tm::PrimApp(Prim::Forall, fa) = quote(&self.e.g, lvl, f) {
                        if fa.len() == 1 {
                            if let Some(b) = self.premise_at(lvl, &fa[0], &names, &sorts) {
                                facts.push(b);
                            }
                        }
                    }
                }
                (g, Sort::Bool)
            }
            _ => {
                let (g, s) = self.term_ctx(lvl, &goal_tm)?;
                match self.extensional(lvl, &goal_tm, &ob.facts)? {
                    Some((ext, at)) => {
                        facts.extend(at);
                        (format!("(or {g} {ext})"), s)
                    }
                    None => (g, s),
                }
            }
        };
        if gs != Sort::Bool {
            return out("a goal that is not a `Bool`");
        }
        let mut dropped = Vec::new();
        let mut ill_typed = Vec::new();
        let mut foralls = false;
        for (k, f) in ob.facts.iter().enumerate() {
            let tm = quote(&self.e.g, lvl, f);
            // A `forall` is used only by name, with `have` (#632), except
            // to check a counterexample.
            if has_forall(&tm) && !self.foralls {
                foralls = true;
                continue;
            }
            // A fact the solver can't see is simply not assumed.
            match self.term_ctx(lvl, &tm) {
                Ok((t, Sort::Bool)) if self.named => facts.push(format!("(! {t} :named |fact.{k}|)")),
                Ok((t, Sort::Bool)) => facts.push(t),
                Ok(_) => {}
                Err(why) if why.is_type_error() => ill_typed.push(k),
                Err(why) => {
                    if !dropped.contains(&why.0) {
                        dropped.push(why.0);
                    }
                }
            }
        }
        self.assume_posts();
        let (defs, opaque_defs, focus) = self.define_instances();
        let reflected = defs.len() != opaque_defs.len() || defs.iter().zip(&opaque_defs).any(|(a, b)| a != b);
        // Definitions may mention new datatypes; postconditions inside them are not assumed.
        let sorts = self.sort_decls()?;
        for (x, id) in std::mem::take(&mut self.real_values) {
            if self.based.contains(&id) {
                self.asserts.push(format!("(not ({} {x}))", base_tester(self.e, id)));
            }
        }
        let mut text = String::new();
        if self.named {
            text += "(set-option :produce-unsat-cores true)\n";
        }
        text += &super::options(super::RLIMIT);
        text += "(set-logic ALL)\n";
        for s in sorts {
            text += &s;
            text += "\n";
        }
        let sorts_end = text.len();
        for f in self.funs.values() {
            if f.starts_with("(declare-fun") {
                text += f;
                text += "\n";
            }
        }
        for f in self.funs.values() {
            if f.starts_with("(define-fun-rec") {
                text += f;
                text += "\n";
            }
        }
        let defs_at = text.len();
        for d in &defs {
            text += d;
            text += "\n";
        }
        let defs_end = text.len();
        let mut axioms = String::new();
        for a in self.axioms.values() {
            axioms += &format!("(assert {a})\n");
        }
        // Last, so that the query with every definition uninterpreted, which
        // has none of what the bodies say, leaves them out.
        let mut body_axioms = String::new();
        for a in self.body_axioms.values() {
            body_axioms += &format!("(assert {a})\n");
        }
        axioms += &body_axioms;
        let split = text.len();
        text += &axioms;
        for c in &self.consts {
            text += c;
            text += "\n";
        }
        for (k, a) in self.asserts.iter().enumerate() {
            text += &if self.named { format!("(assert (! {a} :named |given.{k}|))\n") } else { format!("(assert {a})\n") };
        }
        for a in &facts {
            text += &format!("(assert {a})\n");
        }
        text += &format!("(assert (not {goal}))\n(check-sat)\n");
        if self.named {
            text += "(get-unsat-core)\n";
        }
        if !self.shown.is_empty() {
            text += &format!("(get-value ({}))\n", self.shown.iter().map(|s| s.0.clone()).collect::<Vec<_>>().join(" "));
        }
        // Z3 instantiates a parametric datatype at a sort only once the
        // sort is written: a recognizer at `(Option s)` reached only through
        // another datatype's field (a dictionary's `s -> Option s`) is an
        // unknown constant without it. Declared only where a recognizer
        // comes before the sort is written, so other queries are unchanged
        // (and their cached answers kept).
        let mut written = String::new();
        for (k, s) in self.tested.iter().enumerate() {
            let Sort::Data(id, args) = s else { continue };
            if args.is_empty() {
                continue;
            }
            let r = s.render(self.e);
            let first_test = self.e.g.tys[id.0 as usize].ctors.iter().filter_map(|c| text.find(&format!("({} ", tester(self.e, *c)))).min();
            if first_test.is_some_and(|t| text.find(&r).is_none_or(|w| w > t)) {
                written += &format!("(declare-const |tested#{k}| {r})\n");
            }
        }
        text.insert_str(sorts_end, &written);
        let (defs_at, defs_end, split) = (defs_at + written.len(), defs_end + written.len(), split + written.len());
        let without_axioms = (!axioms.is_empty()).then(|| format!("{}{}", &text[..split], &text[split + axioms.len()..]));
        let body_at = split + axioms.len() - body_axioms.len();
        let without_bodies = (!body_axioms.is_empty()).then(|| format!("{}{}", &text[..body_at], &text[split + axioms.len()..]));
        let facts_only = reflected.then(|| {
            let decls: String = opaque_defs.iter().map(|d| format!("{d}\n")).collect();
            format!("{}{decls}{}{}", &text[..defs_at], &text[defs_end..body_at], &text[split + axioms.len()..])
        });
        let with_defs = |d: String| format!("{}{d}{}{}", &text[..defs_at], &text[defs_end..split], &text[split + axioms.len()..]);
        let focused = focus.mentioned_in(&goal).map(with_defs);
        let premised = focus.mentioned_in(&facts.join("\n")).map(with_defs);
        // Tables' elements go only in the full query: the weaker ones first
        // try without them, and most proofs about a table need only its
        // length (#638).
        let (text, no_tables, without_axioms, without_bodies) = match text.rfind("(assert (not ") {
            Some(k) if !self.table_facts.is_empty() => {
                let full = format!("{}{}{}", &text[..k], self.table_facts.concat(), &text[k..]);
                let lean = without_axioms.or_else(|| Some(text.clone()));
                let without_bodies = without_bodies.map(|t| match t.rfind("(assert (not ") {
                    Some(k) => format!("{}{}{}", &t[..k], self.table_facts.concat(), &t[k..]),
                    None => t,
                });
                (full, Some(text), lean, without_bodies)
            }
            _ => (text, None, without_axioms, without_bodies),
        };
        Ok(Query {
            text,
            no_tables,
            without_axioms,
            without_bodies,
            facts_only,
            focused,
            premised,
            dropped,
            ill_typed,
            foralls,
            shown: self.shown,
            string_vars: self.string_vars,
            array_vars: self.array_vars,
        })
    }
}

/// A dictionary an instance builds, `d a…` (its head a definition): the
/// same application to the variables of an environment of its arguments
/// alone (`d #m-1 … #0`), and their number.
fn dict_over_vars(t: &Tm) -> Option<(Tm, usize)> {
    let mut apps = Vec::new();
    let mut h = t;
    while let Tm::App(f, _, i, m, _) = h {
        apps.push((*i, *m));
        h = f;
    }
    if !matches!(h, Tm::Def(_)) {
        return None;
    }
    apps.reverse();
    let n = apps.len();
    let mut out_ = h.clone();
    for (j, (i, m)) in apps.into_iter().enumerate() {
        out_ = Tm::App(Rc::new(out_), Rc::new(Tm::Var(n - 1 - j)), i, m, crate::core::Pos::NONE);
    }
    Some((out_, n))
}

/// No variable of `t` reaches outside `depth` enclosing binders.
fn closed(t: &Tm, depth: usize) -> bool {
    match t {
        Tm::Var(i) => *i < depth,
        Tm::Meta(_) | Tm::Error => false,
        _ => t.all_sub(|x, n| closed(x, depth + n)),
    }
}

fn smt_bytes(b: &[u8]) -> String {
    if b.is_empty() {
        return "(as seq.empty (Seq Int))".into();
    }
    let units: Vec<String> = b.iter().map(|x| format!("(seq.unit {x})")).collect();
    if units.len() == 1 {
        units[0].clone()
    } else {
        format!("(seq.++ {})", units.join(" "))
    }
}

/// Is a value `Nat`-typed? (for `only_if_nat` obligations)
pub fn is_nat(e: &Elab, ty: &Val) -> bool {
    crate::core::is_nat(&e.g, ty)
}

/// `t` under the conditions `guards`.
/// The definitions `t` names.
fn def_refs(t: &Tm, out: &mut Vec<DefId>) {
    if let Tm::Def(d) = t {
        if !out.contains(d) {
            out.push(*d);
        }
    }
    t.any_sub(|x, _| {
        def_refs(x, out);
        false
    });
}

/// `xs` without repeats, in order.
fn dedup(xs: &mut Vec<String>) {
    let mut seen = HashSet::new();
    xs.retain(|x| seen.insert(x.clone()));
}

fn implies(guards: &[String], t: String) -> String {
    match guards {
        [] => t,
        [g] => format!("(=> {g} {t})"),
        _ => format!("(=> (and {}) {t})", guards.join(" ")),
    }
}

fn has_forall(t: &Tm) -> bool {
    matches!(t, Tm::PrimApp(Prim::Forall, _)) || t.any_sub(|x, _| has_forall(x))
}

/// The elements of `array.from_list [x, y, …]`, if `t` is that.
fn array_literal(e: &Elab, t: &Tm) -> Option<Vec<Tm>> {
    let (head, args) = t.spine();
    let Tm::Def(d) = head else { return None };
    let info = &e.g.defs[d.0 as usize];
    if &*info.module != "std.array" || &*info.name != "from_list" {
        return None;
    }
    let mut list: &Tm = args.last()?;
    let mut out = Vec::new();
    loop {
        match list {
            Tm::ConApp(c, xs) => {
                let name = &e.g.cons[c.0 as usize].name;
                match (&**name, xs.len()) {
                    ("Nil", _) => return Some(out),
                    ("Cons", n) if n >= 2 => {
                        if !closed(&xs[n - 2], 0) {
                            return None;
                        }
                        out.push(xs[n - 2].clone());
                        list = &xs[n - 1];
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
}

/// How many term nodes make a constant large (#640 g).
const LARGE_CONSTANT: usize = 1000;

/// The number of nodes in `t`, counted up to `cap`.
fn tm_size(t: &Tm, cap: usize) -> usize {
    let mut n = 0;
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        n += 1;
        if n >= cap {
            return n;
        }
        match t {
            Tm::App(a, b, ..) | Tm::Pi(_, _, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Lam(_, _, _, b) | Tm::Proj(b, _, _) | Tm::Field(b, _, _, _) => stack.push(b),
            Tm::Let(_, _, a, b, c) => {
                stack.push(a);
                stack.push(b);
                stack.push(c);
            }
            Tm::ConApp(_, v) | Tm::TyConApp(_, v) | Tm::Tuple(v) | Tm::TupleTy(v) | Tm::PrimApp(_, v) => stack.extend(v.iter()),
            Tm::Case(s, c) => {
                stack.push(s);
                stack.extend(c.branches.iter().map(|b| &b.2));
                stack.extend(c.lits.iter().map(|b| &b.1));
                stack.extend(c.default.iter());
            }
            _ => {}
        }
    }
    n
}

/// An integer in SMT-LIB, where a negative number is `(- n)`.
fn smt_int(n: impl Into<num_bigint::BigInt>) -> String {
    let n: num_bigint::BigInt = n.into();
    match n.sign() {
        num_bigint::Sign::Minus => format!("(- {})", n.magnitude()),
        _ => n.to_string(),
    }
}
