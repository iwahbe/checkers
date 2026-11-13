//! `ckc doc FILE`: a module's documentation as JSON lines (§15.6, D131), for
//! `checkers doc`. From the syntax tree alone, so a module with type errors
//! still has documentation:
//!
//! - `{"kind":"module","name":…,"doc":…}`: its name and description (the
//!   comment that opens the file);
//! - `{"kind":"import","module":…,"as":…,"names":[…]}` for each import: the
//!   name the module is used by, and the names it brings in unqualified;
//! - `{"kind":"decl","what":…,"name":…,"line":…,"signature":…,"doc":…,"items":[…]}`
//!   for each exported declaration, in order: what it is (`fn`, `lemma`,
//!   `type`, `enum`, `record`, `let`), its signature as written, its
//!   description (D128), and for an enum or record that isn't abstract, its
//!   constructors or fields (`{"name":…,"signature":…,"doc":…}`).

use crate::json;
use crate::syntax::ast;
use crate::syntax::ast::{Decl, DeclKind, Export, Module};

/// The source from `start` up to the line where `body` starts (all of it
/// without a body), without the comment lines that end it.
fn header(text: &str, start: usize, end: usize, body: Option<usize>) -> String {
    let stop = match body {
        Some(b) => {
            let b = b.min(text.len());
            match text.get(start..b).and_then(|h| h.rfind('\n')) {
                Some(k) => start + k,
                None => b,
            }
        }
        None => end.min(text.len()),
    };
    let mut lines: Vec<&str> = text.get(start..stop).unwrap_or("").lines().collect();
    while lines.len() > 1
        && lines.last().is_some_and(|l| l.trim().is_empty() || l.trim_start().starts_with('#') || l.trim() == "proof")
    {
        lines.pop();
    }
    lines.join("\n").trim_end().to_string()
}

/// The module's description: the run of comment lines that opens the file,
/// without a leading `NAME.ck — ` (how files here name themselves).
fn module_doc(text: &str) -> Option<String> {
    let mut lines = Vec::new();
    for l in text.lines() {
        let t = l.trim();
        let Some(rest) = t.strip_prefix('#') else { break };
        lines.push(rest.strip_prefix(' ').unwrap_or(rest).trim_end().to_string());
    }
    if let Some(first) = lines.first_mut() {
        if let Some(k) = first.find(".ck — ") {
            if !first[..k].contains(' ') {
                let rest = &first[k + ".ck — ".len()..];
                let mut cs = rest.chars();
                *first = match cs.next() {
                    Some(c) => c.to_uppercase().collect::<String>() + cs.as_str(),
                    None => String::new(),
                };
            }
        }
    }
    let doc = lines.join("\n");
    (!doc.trim().is_empty()).then_some(doc)
}

fn string_or_null(s: Option<String>) -> String {
    s.map(|s| json::string(&s)).unwrap_or_else(|| "null".into())
}

fn item(text: &str, name: &str, start: usize, end: usize) -> String {
    format!(
        r#"{{"name":{},"signature":{},"doc":{}}}"#,
        json::string(name),
        json::string(text.get(start..end.min(text.len())).unwrap_or("").trim()),
        string_or_null(crate::doc_comment(text, start)),
    )
}

/// One declaration's line, if it is exported and documented at all.
fn decl(text: &str, d: &Decl, line_of: &dyn Fn(usize) -> usize) -> Option<String> {
    if d.export == Export::No {
        return None;
    }
    let start = d.span.start as usize;
    let end = d.span.end as usize;
    let (what, name, body, items): (&str, &str, Option<usize>, Vec<String>) = match &d.kind {
        DeclKind::Fn { name, body, decreasing, .. } => {
            let b = decreasing.as_ref().map(|e| e.span.start).unwrap_or(body.span.start);
            ("fn", &name.name, Some(b as usize), Vec::new())
        }
        DeclKind::Lemma { name, proof, .. } => ("lemma", &name.name, proof.as_ref().map(|p| p.span.start as usize), Vec::new()),
        DeclKind::Alias { name, .. } => ("type", &name.name, None, Vec::new()),
        DeclKind::Enum { name, ctors, .. } => {
            let items = if d.export == Export::Abstract {
                Vec::new()
            } else {
                ctors.iter().map(|c| item(text, &c.name.name, c.span.start as usize, c.span.end as usize)).collect()
            };
            ("enum", &name.name, ctors.first().map(|c| c.span.start as usize), items)
        }
        DeclKind::Record { name, fields, .. } => {
            let items = if d.export == Export::Abstract {
                Vec::new()
            } else {
                fields.iter().map(|f| item(text, &f.name.name, f.span.start as usize, f.span.end as usize)).collect()
            };
            ("record", &name.name, fields.first().map(|f| f.span.start as usize), items)
        }
        DeclKind::Const { name, .. } => {
            // A long value (a table, say) is shown only by its name.
            let whole = text.get(start..end.min(text.len())).unwrap_or("").trim();
            let sig = if whole.contains('\n') || whole.len() > 100 {
                let export = whole.split(&format!("let {}", name.name)).next().unwrap_or("");
                format!("{export}let {} = …", name.name)
            } else {
                whole.to_string()
            };
            return Some(format!(
                r#"{{"kind":"decl","what":"let","name":{},"line":{},"signature":{},"doc":{},"items":[]}}"#,
                json::string(&name.name),
                line_of(start),
                json::string(&sig),
                string_or_null(crate::doc_comment(text, start)),
            ));
        }
        DeclKind::Check { .. } | DeclKind::Instance { .. } => return None,
        DeclKind::Class { name, members, .. } => {
            let items = members
                .iter()
                .map(|m| match m {
                    ast::ClassMember::Fn { name, span, .. } | ast::ClassMember::Lemma { name, span, .. } => {
                        item(text, &name.name, span.start as usize, span.end as usize)
                    }
                })
                .collect();
            let first = members.first().map(|m| match m {
                ast::ClassMember::Fn { span, .. } | ast::ClassMember::Lemma { span, .. } => span.start as usize,
            });
            ("class", &name.name, first, items)
        }
    };
    Some(format!(
        r#"{{"kind":"decl","what":"{what}","name":{},"line":{},"signature":{},"doc":{},"items":[{}]}}"#,
        json::string(name),
        line_of(start),
        json::string(&header(text, start, end, body)),
        string_or_null(crate::doc_comment(text, start)),
        items.join(","),
    ))
}

/// The documentation of `module` (parsed from `text`), as JSON lines.
pub fn lines(text: &str, module: &Module, fallback_name: &str) -> Vec<String> {
    let name = module.name.as_ref().map(|q| q.dotted()).unwrap_or_else(|| fallback_name.to_string());
    let line_of = |at: usize| text[..at.min(text.len())].matches('\n').count() + 1;
    let mut out =
        vec![format!(r#"{{"kind":"module","name":{},"doc":{}}}"#, json::string(&name), string_or_null(module_doc(text)))];
    for i in &module.imports {
        let path = i.path.dotted();
        let used_as = match &i.alias {
            Some(a) => a.name.to_string(),
            None => i.path.parts.last().map(|p| p.name.to_string()).unwrap_or_default(),
        };
        let names: Vec<String> = i.items.iter().flatten().map(|n| json::string(&n.name)).collect();
        out.push(format!(
            r#"{{"kind":"import","module":{},"as":{},"names":[{}]}}"#,
            json::string(&path),
            json::string(&used_as),
            names.join(",")
        ));
    }
    out.extend(module.decls.iter().filter_map(|d| decl(text, d, &line_of)));
    out
}
