//! Doc comments as literate documentation (D148 e, f): their `[name]` links
//! and their Checkers code blocks, checked with the module they describe.
//!
//! `ckc check` doesn't parse doc comments as full CommonMark (that is
//! `std.markdown`, which `checkers doc` uses): it finds fenced code blocks
//! (```` ``` ```` or `~~~` fences) and bracketed references outside code, which
//! is what doc comments use. A link resolves in the module's scope: its
//! declarations, its imports and the prelude; W030 if it names nothing, W031
//! if what it names isn't exported. A block is checked as a module of its
//! own, beside the file (W032 for what it reports, at its place in the
//! comment; W033 for a `compile_fail` block that compiles, or fails with
//! another error). Running blocks (W034) is `checkers doc`'s.

use crate::diag::Diagnostic;
use crate::elab::index::Target;
use crate::elab::{Elab, Sym};
use crate::source::Span;
use crate::syntax::ast::{DeclKind, Module};

/// A line of a doc comment: its text without `#` and one space, and where
/// that text starts in the file.
#[derive(Clone)]
pub struct Line {
    pub text: String,
    pub at: usize,
}

/// A fenced code block in a doc comment: its info string, its lines, and
/// where its opening fence is.
pub struct Block {
    pub info: String,
    pub lines: Vec<Line>,
    pub fence: usize,
}

/// A bracketed reference: its label (as written) and its span.
pub struct Ref {
    pub label: String,
    pub span: Span,
}

/// A block as the module that is checked: its name, its text, and for each
/// of its lines where that line's first byte is in the file.
pub struct Sample {
    pub name: String,
    pub text: String,
    pub starts: Vec<usize>,
    pub info: String,
    /// Whether its first line is a `module` line it was given.
    pub inserted: bool,
}

/// The doc comments of `module` (its opening comment, and the comment lines
/// directly above each declaration, constructor, field and class member).
pub fn regions(text: &str, module: &Module) -> Vec<Vec<Line>> {
    let mut starts: Vec<usize> = Vec::new();
    for d in &module.decls {
        starts.push(d.span.start as usize);
        match &d.kind {
            DeclKind::Enum { ctors, .. } => starts.extend(ctors.iter().map(|c| c.span.start as usize)),
            DeclKind::Record { fields, .. } => starts.extend(fields.iter().map(|f| f.span.start as usize)),
            DeclKind::Class { members, .. } => starts.extend(members.iter().map(|m| match m {
                crate::syntax::ast::ClassMember::Fn { span, .. } | crate::syntax::ast::ClassMember::Lemma { span, .. } => {
                    span.start as usize
                }
            })),
            _ => {}
        }
    }
    let mut out: Vec<Vec<Line>> = Vec::new();
    let opening = comment_run_after(text, 0);
    if !opening.is_empty() {
        out.push(opening);
    }
    for s in starts {
        let r = comment_run_before(text, s);
        if !r.is_empty() && !out.iter().any(|o| o[0].at == r[0].at) {
            out.push(r);
        }
    }
    out.sort_by_key(|r| r[0].at);
    out
}

/// The comment line at `start` (a line's first byte), if it is one.
fn comment_line(text: &str, start: usize) -> Option<Line> {
    let end = text[start..].find('\n').map_or(text.len(), |k| start + k);
    let line = &text[start..end];
    let indent = line.len() - line.trim_start().len();
    let rest = line.trim_start().strip_prefix('#')?;
    let skip = if rest.starts_with(' ') { 1 } else { 0 };
    let body = rest[skip..].trim_end_matches('\r');
    Some(Line { text: body.to_string(), at: start + indent + 1 + skip })
}

fn comment_run_after(text: &str, mut start: usize) -> Vec<Line> {
    let mut out = Vec::new();
    while start < text.len() {
        let Some(l) = comment_line(text, start) else { break };
        out.push(l);
        match text[start..].find('\n') {
            Some(k) => start += k + 1,
            None => break,
        }
    }
    out
}

fn comment_run_before(text: &str, at: usize) -> Vec<Line> {
    let mut start = text[..at.min(text.len())].rfind('\n').map_or(0, |i| i + 1);
    let mut out = Vec::new();
    while start > 0 {
        let prev = text[..start - 1].rfind('\n').map_or(0, |i| i + 1);
        let Some(l) = comment_line(text, prev) else { break };
        out.push(l);
        start = prev;
    }
    out.reverse();
    out
}

/// A fence at the start of `text` (up to 3 spaces first): its character and
/// length, and the rest of the line.
fn fence(text: &str) -> Option<(char, usize, &str)> {
    let t = text.trim_start_matches(' ');
    if text.len() - t.len() > 3 {
        return None;
    }
    let c = t.chars().next()?;
    if c != '`' && c != '~' {
        return None;
    }
    let n = t.chars().take_while(|x| *x == c).count();
    if n < 3 {
        return None;
    }
    let rest = &t[n..];
    if c == '`' && rest.contains('`') {
        return None;
    }
    Some((c, n, rest))
}

/// The code blocks and references in a doc comment.
pub fn scan(region: &[Line]) -> (Vec<Block>, Vec<Ref>) {
    let mut blocks = Vec::new();
    let mut refs = Vec::new();
    let defined: Vec<String> = region.iter().filter_map(|l| definition_label(&l.text)).collect();
    let mut i = 0;
    while i < region.len() {
        let l = &region[i];
        if let Some((c, n, info)) = fence(&l.text) {
            let mut lines = Vec::new();
            let mut j = i + 1;
            while j < region.len() {
                let t = region[j].text.trim();
                if t.chars().all(|x| x == c) && t.len() >= n {
                    break;
                }
                lines.push(region[j].clone());
                j += 1;
            }
            blocks.push(Block { info: info.trim().to_string(), lines, fence: l.at });
            i = j + 1;
            continue;
        }
        if definition_label(&l.text).is_none() {
            line_refs(l, &defined, &mut refs);
        }
        i += 1;
    }
    (blocks, refs)
}

/// The label of a link reference definition (`[label]: url`) on the line.
fn definition_label(text: &str) -> Option<String> {
    let t = text.trim_start();
    let rest = t.strip_prefix('[')?;
    let close = rest.find("]:")?;
    Some(normalize(&rest[..close]))
}

fn normalize(label: &str) -> String {
    label.split_whitespace().collect::<Vec<_>>().join(" ").to_lowercase()
}

/// The references on a line: `[label]`, `[text][label]` and `[label][]`,
/// outside code spans, other than inline links and defined labels.
fn line_refs(l: &Line, defined: &[String], out: &mut Vec<Ref>) {
    let b = l.text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'\\' => i += 2,
            b'`' => {
                let n = b[i..].iter().take_while(|c| **c == b'`').count();
                let ticks = &l.text[i..i + n];
                match l.text[i + n..].find(ticks) {
                    Some(k) => i += n + k + n,
                    None => i += n,
                }
            }
            b'[' => {
                let Some(close) = bracket_end(b, i + 1) else {
                    i += 1;
                    continue;
                };
                let text = &l.text[i + 1..close];
                let after = close + 1;
                if b.get(after) == Some(&b'(') {
                    i = after;
                    continue;
                }
                let (label, end, at) = if b.get(after) == Some(&b'[') {
                    match bracket_end(b, after + 1) {
                        Some(c2) if c2 > after + 1 => (&l.text[after + 1..c2], c2 + 1, after),
                        Some(c2) => (text, c2 + 1, i),
                        None => (text, after, i),
                    }
                } else {
                    (text, after, i)
                };
                if !defined.contains(&normalize(label)) && !text.contains('[') {
                    out.push(Ref { label: label.to_string(), span: Span::new(l.at + at, l.at + end) });
                }
                i = end;
            }
            _ => i += 1,
        }
    }
}

/// The `]` closing a bracket opened before `i`, skipping escapes and code.
fn bracket_end(b: &[u8], mut i: usize) -> Option<usize> {
    while i < b.len() {
        match b[i] {
            b'\\' => i += 2,
            b']' => return Some(i),
            b'[' => return None,
            _ => i += 1,
        }
    }
    None
}

/// A label as a dotted path of names, without the backticks that show it
/// as code.
fn path_of(label: &str) -> Option<Vec<&str>> {
    let t = label.trim();
    let t = if t.len() > 2 && t.starts_with('`') && t.ends_with('`') { &t[1..t.len() - 1] } else { t };
    let parts: Vec<&str> = t.split('.').collect();
    let ok = parts.iter().all(|p| {
        let mut cs = p.chars();
        matches!(cs.next(), Some(c) if c.is_ascii_alphabetic() || c == '_') && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
    });
    ok.then_some(parts)
}

/// Whether `info` marks a Checkers block: no language, or `checkers`.
pub fn is_checkers(info: &str) -> bool {
    let lang = info.split_whitespace().next().unwrap_or("").split(',').next().unwrap_or("");
    lang.is_empty() || lang == "checkers"
}

fn attrs(info: &str) -> Vec<&str> {
    info.split_whitespace().next().unwrap_or("").split(',').skip(1).map(|a| a.trim()).collect()
}

/// A block as a module: `#!` lines compiled but not shown, and a hidden
/// `module` line if it has none.
pub fn sample(b: &Block, k: usize) -> Sample {
    let mut lines: Vec<(String, usize)> = Vec::new();
    for l in &b.lines {
        if let Some(rest) = l.text.strip_prefix("#!") {
            let skip = if rest.starts_with(' ') { 1 } else { 0 };
            lines.push((rest[skip..].to_string(), l.at + 2 + skip));
        } else {
            lines.push((l.text.clone(), l.at));
        }
    }
    let named = lines
        .iter()
        .map(|(t, _)| t.trim())
        .find(|t| !t.is_empty() && !t.starts_with('#'))
        .and_then(|t| t.strip_prefix("module "))
        .map(|n| n.trim().to_string());
    let inserted = named.is_none();
    let name = match named {
        Some(n) => n,
        None => {
            let n = format!("doc_sample_{k}");
            lines.insert(0, (format!("module {n}"), b.fence));
            n
        }
    };
    let text = lines.iter().map(|(t, _)| format!("{t}\n")).collect::<String>();
    Sample { name, text, starts: lines.iter().map(|(_, a)| *a).collect(), info: b.info.clone(), inserted }
}

impl Sample {
    /// Where byte `offset` of the sample's text is in the file.
    pub fn place(&self, offset: usize) -> usize {
        let mut start = 0;
        for (j, line) in self.text.split_inclusive('\n').enumerate() {
            if offset < start + line.len() || j + 1 == self.starts.len() {
                return self.starts.get(j).copied().unwrap_or(0) + offset.saturating_sub(start);
            }
            start += line.len();
        }
        self.starts.last().copied().unwrap_or(0)
    }

    /// Where line `line`, column `col` (bytes, from 0) of the sample is in
    /// the file.
    pub fn place_at(&self, line: usize, col: usize) -> usize {
        self.starts.get(line).copied().unwrap_or(0) + col
    }
}

/// What a path names from module `user`: `Some(exported)`, or `None`.
fn resolve(e: &Elab, user: &str, parts: &[&str]) -> Option<bool> {
    let m = e.modules.get(user)?;
    if e.modules.contains_key(&parts.join(".")) {
        return Some(true);
    }
    let prelude = e.modules.get("std.prelude");
    if parts.len() == 1 {
        let n = parts[0];
        if m.values.contains_key(n) || m.types.contains_key(n) {
            return Some(m.exported_values.contains(n) || m.exported_types.contains(n));
        }
        if m.import_values.contains_key(n) || m.import_types.contains_key(n) {
            return Some(true);
        }
        if let Some(p) = prelude {
            if p.exported_values.contains(n) || p.exported_types.contains(n) {
                return Some(true);
            }
        }
        return None;
    }
    // A qualifier or a module's full name, then what is in it.
    for k in (1..parts.len()).rev() {
        let prefix = parts[..k].join(".");
        let module = if k == 1 && m.qualifiers.contains_key(&prefix) {
            m.qualifiers.get(&prefix).cloned()
        } else if e.modules.contains_key(&prefix) {
            Some(prefix)
        } else {
            None
        };
        if let Some(x) = module {
            return resolve_in(e, &x, &parts[k..]);
        }
    }
    // `Type.member`: a constructor or a field.
    if parts.len() == 2 {
        let ty = m.types.get(parts[0]).or_else(|| m.import_types.get(parts[0])).or_else(|| prelude.and_then(|p| p.types.get(parts[0])));
        if let Some(Sym::Ty(t)) = ty {
            if has_member(e, *t, parts[1]) {
                return Some(m.exported_types.contains(parts[0]) || !m.types.contains_key(parts[0]));
            }
        }
    }
    None
}

fn resolve_in(e: &Elab, module: &str, rest: &[&str]) -> Option<bool> {
    let x = e.modules.get(module)?;
    match rest {
        [n] if x.values.contains_key(*n) || x.types.contains_key(*n) => {
            Some(x.exported_values.contains(*n) || x.exported_types.contains(*n))
        }
        [t, member] => match x.types.get(*t) {
            Some(Sym::Ty(id)) if has_member(e, *id, member) => Some(x.exported_types.contains(*t)),
            _ => None,
        },
        _ => None,
    }
}

fn has_member(e: &Elab, t: crate::core::TyId, member: &str) -> bool {
    e.g.tys[t.0 as usize].ctors.iter().any(|c| {
        let ci = &e.g.cons[c.0 as usize];
        ci.name.as_ref() == member || ci.fields.iter().any(|f| f.0.as_ref() == member)
    })
}

/// The names a link's path looks up, from where it starts.
type Scope<'a> = Box<dyn Fn(&str) -> Option<Sym> + 'a>;

/// The declarations a link names (D161): each part of its path that is a
/// declaration, a constructor or a field, with its span in the file, so
/// that renaming one renames it in the link too.
pub fn link_targets(e: &Elab, user: &str, r: &Ref) -> Vec<(Span, Target)> {
    let mut out = Vec::new();
    let Some(parts) = path_of(&r.label) else { return out };
    let Some(m) = e.modules.get(user) else { return out };
    // Where the label's text starts: after `[`, its spaces and a backtick.
    let lead = r.label.len() - r.label.trim_start().len();
    let tick = usize::from(r.label.trim().len() > 2 && r.label.trim().starts_with('`'));
    let mut at = r.span.start as usize + 1 + lead + tick;
    let mut spans = Vec::new();
    for p in &parts {
        spans.push(Span::new(at, at + p.len()));
        at += p.len() + 1;
    }
    let sym_target = |s: &Sym| match s {
        Sym::Def(d) => Some(Target::Def(*d)),
        Sym::Ty(t) => Some(Target::Ty(*t)),
        Sym::Con(c) => Some(Target::Con(*c)),
        _ => None,
    };
    let in_scope = |n: &str| -> Option<Sym> {
        m.types
            .get(n)
            .or_else(|| m.import_types.get(n))
            .or_else(|| m.values.get(n))
            .or_else(|| m.import_values.get(n))
            .or_else(|| e.modules.get("std.prelude").and_then(|p| p.types.get(n).or_else(|| p.values.get(n))))
            .copied()
    };
    let member = |t: crate::core::TyId, n: &str| -> Option<Target> {
        for c in &e.g.tys[t.0 as usize].ctors {
            let ci = &e.g.cons[c.0 as usize];
            if ci.name.as_ref() == n {
                return Some(Target::Con(*c));
            }
            if let Some(k) = ci.fields.iter().position(|f| f.0.as_ref() == n) {
                return Some(Target::Field(*c, k));
            }
        }
        None
    };
    // A qualifier or a module's name, then what is in it.
    let mut from = None;
    for k in (1..parts.len()).rev() {
        let prefix = parts[..k].join(".");
        let module = if k == 1 && m.qualifiers.contains_key(&prefix) { m.qualifiers.get(&prefix).cloned() } else { e.modules.contains_key(&prefix).then_some(prefix) };
        if let Some(x) = module {
            from = Some((x, k));
            break;
        }
    }
    let (scope, k): (Scope, usize) = match from {
        Some((x, k)) => {
            let Some(xm) = e.modules.get(&x) else { return out };
            (Box::new(move |n: &str| xm.types.get(n).or_else(|| xm.values.get(n)).copied()), k)
        }
        None => (Box::new(in_scope), 0),
    };
    let Some(first) = parts.get(k) else { return out };
    let Some(s) = scope(first) else { return out };
    if let Some(t) = sym_target(&s) {
        out.push((spans[k], t));
    }
    if let (Sym::Ty(t), Some(n)) = (s, parts.get(k + 1)) {
        if let Some(x) = member(t, n) {
            out.push((spans[k + 1], x));
        }
    }
    out
}

/// The names a reference may complete to after `[` in a doc comment: the
/// module's own, its imports' and the prelude's, with what each is (D148 f).
pub fn link_names(e: &Elab, user: &str) -> Vec<(String, &'static str)> {
    let mut out: Vec<(String, &'static str)> = Vec::new();
    let class = |s: &Sym| match s {
        Sym::Ty(_) => "type",
        Sym::Con(_) => "constructor",
        _ => "function",
    };
    let mut add = |m: &crate::elab::ModuleInfo| {
        for (n, s) in m.values.iter().chain(m.types.iter()).chain(m.import_values.iter()).chain(m.import_types.iter()) {
            out.push((n.clone(), class(s)));
        }
        for q in m.qualifiers.keys() {
            out.push((q.clone(), "module"));
        }
    };
    if let Some(m) = e.modules.get(user) {
        add(m);
    }
    out.sort();
    out.dedup_by(|a, b| a.0 == b.0);
    out
}

/// W030 and W031 for the doc comments' links, and the samples their
/// Checkers blocks make (`ignore` ones left out).
pub fn links_and_samples(text: &str, module: &Module, e: &Elab, user: &str) -> (Vec<Diagnostic>, Vec<Sample>) {
    let mut diags = Vec::new();
    let mut samples = Vec::new();
    for region in regions(text, module) {
        let (blocks, refs) = scan(&region);
        for r in refs {
            let Some(parts) = path_of(&r.label) else { continue };
            let shown = parts.join(".");
            match resolve(e, user, &parts) {
                Some(true) => {}
                Some(false) => diags.push(Diagnostic::warning(
                    "W031",
                    format!("`{shown}` isn't exported, so it has no documentation to link to"),
                    r.span,
                )
                .with_label("not exported")),
                None => diags.push(
                    Diagnostic::warning("W030", format!("no symbol `{shown}` to link to"), r.span)
                        .with_label("not found")
                        .with_help("a link names a declaration, a module, or a constructor or field (`Type.name`) in this module's scope; write `\\[` for a bracket that isn't one"),
                ),
            }
        }
        for b in blocks {
            if is_checkers(&b.info) && !attrs(&b.info).contains(&"ignore") {
                samples.push(sample(&b, samples.len() + 1));
            }
        }
    }
    (diags, samples)
}

/// What checking a sample says, as W032 or W033 at its place in the file.
pub fn sample_diagnostics(s: &Sample, dir: &std::path::Path) -> Vec<Diagnostic> {
    let c = crate::check_in(&format!("{}.ck", s.name), &s.text, dir);
    let fence = s.starts.first().copied().unwrap_or(0);
    let here = Span::new(fence, fence);
    let a = attrs(&s.info);
    if a.contains(&"compile_fail") {
        let code = a.iter().find(|x| x.len() == 5 && x.starts_with('E')).copied();
        if c.errors() == 0 {
            return vec![Diagnostic::warning("W033", "this example compiles, but is marked `compile_fail`", here)
                .with_help("remove `compile_fail`, or make the example fail")];
        }
        if let Some(code) = code {
            if !c.diags.iter().any(|d| d.code == code) {
                let got: Vec<&str> = c.diags.iter().filter(|d| d.is_error()).map(|d| d.code).collect();
                return vec![Diagnostic::warning("W033", format!("this example fails, but not with {code}"), here)
                    .with_note(format!("it fails with {}", got.join(", ")))];
            }
        }
        return Vec::new();
    }
    let mut out: Vec<Diagnostic> = c
        .diags
        .iter()
        .map(|d| {
            let start = s.place(d.span.start as usize);
            let end = s.place((d.span.end as usize).max(d.span.start as usize));
            let mut w = Diagnostic::warning("W032", format!("this example has {}[{}]: {}", kind(d), d.code, d.message), Span::new(start, end));
            w.label = d.label.clone();
            w.notes = d.notes.clone();
            w.help = d.help.clone();
            w
        })
        .collect();
    for (name, _, ds) in &c.others {
        for d in ds {
            out.push(Diagnostic::warning("W032", format!("this example's import `{name}` has {}[{}]: {}", kind(d), d.code, d.message), here));
        }
    }
    out
}

fn kind(d: &Diagnostic) -> &'static str {
    if d.is_error() {
        "error"
    } else {
        "warning"
    }
}
