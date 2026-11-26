//! The Checkers compiler. See SPEC.md for the language definition.
//!
//! Pipeline: lex (with layout) → parse → naming lints → elaborate and
//! type-check (with the embedded standard library) → termination and usage →
//! run `check`s (D40). `run` then erases and interprets the program (§13).

pub mod core;
pub mod diag;
pub mod doc;
pub mod elab;
pub mod json;
pub mod lint;
pub mod literate;
pub mod native;
pub mod overlay;
pub mod range;
pub mod source;
pub mod stage;
pub mod syntax;
pub mod usage;
pub mod verify;

use diag::Diagnostic;
use source::SourceFile;

/// Result of checking one file.
pub struct Checked {
    pub file: SourceFile,
    pub module: syntax::ast::Module,
    pub diags: Vec<Diagnostic>,
    /// Diagnostics in standard-library modules (compiler bugs), already rendered.
    pub internal: Vec<String>,
    /// Diagnostics in imported program modules (D53), with their files.
    pub others: Vec<(String, SourceFile, Vec<Diagnostic>)>,
    /// Proof obligations in this file, and how many the prover discharged.
    pub obligations: usize,
    pub proved: usize,
    /// The trust ledger (§7.4), rendered.
    pub ledger: String,
    /// Staged definitions (§8.9), for `checkers stage`.
    pub staged: String,
    /// The modules verified before, by name (D143), once looked up.
    remembered: Option<std::collections::HashMap<String, (String, verify::Remembered)>>,
}

impl Checked {
    fn all_diags(&self) -> impl Iterator<Item = &Diagnostic> {
        self.others.iter().flat_map(|o| o.2.iter()).chain(self.diags.iter())
    }

    pub fn errors(&self) -> usize {
        self.all_diags().filter(|d| d.is_error()).count() + self.internal.len()
    }

    pub fn warnings(&self) -> usize {
        self.all_diags().filter(|d| !d.is_error()).count()
    }

    /// Diagnostics in source order (imported modules first), then a one-line summary.
    pub fn report(&self) -> String {
        // Each module's diagnostics, a blank line between them and before the summary.
        let mut parts: Vec<String> = Vec::new();
        for (_, f, ds) in &self.others {
            if !ds.is_empty() {
                parts.push(diag::render_all(f, ds));
            }
        }
        if !self.diags.is_empty() {
            parts.push(diag::render_all(&self.file, &self.diags));
        }
        parts.extend(self.internal.iter().cloned());
        let mut out = parts.join("\n");
        if !out.is_empty() {
            out.push('\n');
        }
        out += &format!(
            "{}: {} error{}, {} warning{}",
            self.file.name,
            self.errors(),
            if self.errors() == 1 { "" } else { "s" },
            self.warnings(),
            if self.warnings() == 1 { "" } else { "s" },
        );
        if self.proved > 0 && self.errors() == 0 {
            out += &format!("; {} obligation{} proved", self.proved, if self.proved == 1 { "" } else { "s" });
        }
        out.push('\n');
        out
    }
}

/// Lex, parse and lint only.
pub fn parse_only(name: &str, text: &str) -> Checked {
    let file = SourceFile::new(name, text);
    let (module, mut diags) = syntax::parse_module(text);
    diags.extend(lint::naming(&module));
    Checked { file, module, diags, internal: Vec::new(), others: Vec::new(), obligations: 0, proved: 0, ledger: String::new(), staged: String::new(), remembered: None }
}

/// The directory `import a.b` looks in for `a/b.ck` (D53): the program's own.
pub fn dir_of(name: &str) -> std::path::PathBuf {
    std::path::Path::new(name).parent().map(|p| p.to_path_buf()).unwrap_or_default()
}

/// Run every implemented phase over one source file, including its `check`s
/// and proofs, and those of every module it imports.
pub fn check(name: &str, text: &str) -> Checked {
    check_in(name, text, &dir_of(name))
}

/// `check`, with imported modules looked up in `dir`.
pub fn check_in(name: &str, text: &str, dir: &std::path::Path) -> Checked {
    let t = std::time::Instant::now();
    let (mut c, e) = elaborate(name, text, dir);
    phase_time(name, "types", t);
    if let Some((e, user)) = &e {
        let t = std::time::Instant::now();
        doc_comments(&mut c, e, user, dir);
        phase_time(name, "doc comments", t);
        let t = std::time::Instant::now();
        run_checks(&mut c, e, user);
        phase_time(name, "checks", t);
        let t = std::time::Instant::now();
        prove(&mut c, e, user);
        phase_time(name, "proofs", t);
        stage_module(&mut c, e, user);
    }
    c
}

/// `CHECKERS_PHASE_TIME=1`: each phase's time, for each file checked (a doc
/// comment's example too).
fn phase_time(name: &str, phase: &str, t: std::time::Instant) {
    if std::env::var_os("CHECKERS_PHASE_TIME").is_some() {
        eprintln!("{name}: {phase} {:.1} ms", t.elapsed().as_secs_f64() * 1000.0);
    }
}

/// `ckc check --json` (§15.5, D120): check `name` like `check_in`, writing
/// JSON lines to `out` as each phase ends: syntax, names and types; `check`s;
/// proofs. Every phase ends with a `done` line, also when an earlier phase's
/// errors mean it does nothing. Returns whether there were errors.
pub fn check_json(name: &str, text: &str, dir: &std::path::Path, out: &mut dyn FnMut(String)) -> bool {
    let main = overlay::absolute(std::path::Path::new(name));
    let (mut c, e) = elaborate(name, text, dir);
    let mut seen: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let user = e.as_ref().map(|(_, u)| u.clone()).unwrap_or_default();
    emit_new(&c, e.as_ref().map(|x| &x.0), &main, "types", &mut seen, out);
    out(r#"{"kind":"done","phase":"types"}"#.to_string());
    // The index after the types phase's diagnostics, so they aren't kept
    // waiting by it.
    match &e {
        Some((e, user)) => {
            // The doc comments' code is indexed as code (D148 f): their
            // lines' comment tokens give way to its tokens.
            let samples = literate::links_and_samples(&c.file.text, &c.module, e, user).1;
            // Each code line's start: its comment marker (`#`, and `#!`
            // on a hidden line) stays a comment, the rest is code. A
            // `module` line given to a block is no line of the file.
            let covered: std::collections::HashMap<usize, usize> = samples
                .iter()
                .flat_map(|s| s.starts.iter().enumerate().filter(|(i, _)| !s.given.contains(i)).map(|(_, a)| c.file.line_byte(*a as u32)))
                .collect();
            let mut kept = |l: String| {
                let here = if l.contains(r#""class":"comment""#) { start_line(&l).and_then(|n| covered.get(&n).map(|col| (n, *col))) } else { None };
                match here {
                    None => out(l),
                    Some((n, col)) => {
                        // The comment's start column, from `"start":[n,c]`.
                        let key = format!(r#""start":[{n},"#);
                        let from = l.find(&key).and_then(|k| l[k + key.len()..].split(']').next()?.parse::<usize>().ok());
                        let path = l.split(r#""path":"#).nth(1).and_then(|r| r.split(r#","start""#).next()).unwrap_or("\"\"");
                        if let Some(c0) = from.filter(|c0| *c0 < col) {
                            out(format!(r#"{{"kind":"token","path":{path},"start":[{n},{c0}],"end":[{n},{col}],"class":"comment"}}"#));
                        }
                    }
                }
            };
            emit_index(e, user, &main, &mut kept);
            let root = e.base_dir.clone().unwrap_or_else(|| dir.to_path_buf());
            for s in &samples {
                emit_sample_index(&c.file, s, &root, &main, out);
            }
        }
        None => emit_tokens(&main, &c.file, out),
    }
    out(r#"{"kind":"done","phase":"index"}"#.to_string());
    if let Some((e, user)) = &e {
        doc_comments(&mut c, e, user, dir);
        run_checks(&mut c, e, user);
    }
    emit_new(&c, e.as_ref().map(|x| &x.0), &main, "checks", &mut seen, out);
    out(r#"{"kind":"done","phase":"checks"}"#.to_string());
    if let Some((e, user)) = &e {
        prove(&mut c, e, user);
        stage_module(&mut c, e, user);
    }
    emit_new(&c, e.as_ref().map(|x| &x.0), &main, "proofs", &mut seen, out);
    out(r#"{"kind":"done","phase":"proofs"}"#.to_string());
    let _ = user;
    c.errors() > 0
}

/// `ckc index` (D161): the index of every module of the package `name`'s
/// module is in, as `check --json` gives one file's: its names and tokens,
/// then `done`. The package is the directory its module's name is relative
/// to (`a/b.ck` is `a.b`, D53), and every `.ck` file under it. Names and
/// types only: nothing is run or proved.
pub fn index_json(name: &str, text: &str, out: &mut dyn FnMut(String)) {
    let main = overlay::absolute(std::path::Path::new(name));
    let (m, _) = syntax::parse_module(text);
    let depth = m.name.as_ref().map(|q| q.dotted().split('.').count()).unwrap_or(1);
    let mut root = main.parent().map(|p| p.to_path_buf()).unwrap_or_default();
    for _ in 1..depth {
        root = root.parent().map(|p| p.to_path_buf()).unwrap_or(root);
    }
    fn walk(base: &std::path::Path, dir: &std::path::Path, out: &mut Vec<String>) {
        let Ok(rd) = std::fs::read_dir(dir) else { return };
        let mut entries: Vec<_> = rd.flatten().map(|e| e.path()).collect();
        entries.sort();
        for p in entries {
            let file = p.file_name().map(|f| f.to_string_lossy().to_string()).unwrap_or_default();
            if file.starts_with('.') || file == "target" {
                continue;
            }
            if p.is_dir() {
                walk(base, &p, out);
            } else if p.extension().is_some_and(|x| x == "ck") {
                if let Ok(rel) = p.strip_prefix(base) {
                    let parts: Vec<String> = rel.with_extension("").iter().map(|c| c.to_string_lossy().to_string()).collect();
                    // Only names a module can have (§9.1).
                    if parts.iter().all(|s| s.chars().next().is_some_and(|c| c.is_ascii_lowercase()) && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')) {
                        out.push(parts.join("."));
                    }
                }
            }
        }
    }
    let mut names = Vec::new();
    walk(&root, &root, &mut names);
    let mut e = elab::Elab::new();
    e.base_dir = Some(root.clone());
    for core in ["std.prelude", "std.cown", "std.future", "std.system"] {
        e.load_stdlib(core);
    }
    e.index_all = Some(names.iter().cloned().collect());
    for n in &names {
        if !e.modules.contains_key(n) {
            e.load_user(n, source::Span::default());
        }
    }
    let first = names.first().cloned().unwrap_or_default();
    emit_index_all(&e, &first, out);
    // The code in their doc comments, as `check --json` indexes it (D148 f).
    for n in &names {
        let (Some(f), Some(p)) = (e.sources.get(n), e.paths.get(n)) else { continue };
        let (module, _) = syntax::parse_module(&f.text);
        for s in literate::links_and_samples(&f.text, &module, &e, n).1 {
            emit_sample_index(f, &s, &root, p, out);
        }
    }
    out(r#"{"kind":"done","phase":"index"}"#.to_string());
}

/// `ckc complete` (§15.5, D142): what can be written at byte column `col`
/// of line `line` (from 0) of `name`, as JSON lines: the span the
/// completion replaces, then each candidate in order, then `done`. The
/// names and types phase runs, with a cursor token there; nothing else.
pub fn complete_json(name: &str, text: &str, dir: &std::path::Path, line: usize, col: usize, out: &mut dyn FnMut(String)) {
    let file = SourceFile::new(name, text);
    let main = overlay::absolute(std::path::Path::new(name));
    let at = file.offset(line, col);
    if let Some(at) = at {
        if complete_in_doc(name, &file, dir, &main, at, out) {
            return;
        }
    }
    let parsed = at.and_then(|at| syntax::parse_at_cursor(text, at));
    if let Some((module, Some(place), replaced)) = parsed {
        let stem = std::path::Path::new(name).file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
        let e = elab::check_module_at(&stem, &file, &module, Some(dir), Some(replaced.start));
        let user = module.name.as_ref().map(|q| q.dotted()).unwrap_or(stem);
        let (sl, sc) = file.line_byte(replaced.start);
        let (el, ec) = file.line_byte(replaced.end);
        out(format!(
            r#"{{"kind":"complete","path":{},"start":[{sl},{sc}],"end":[{el},{ec}]}}"#,
            json::string(&main.to_string_lossy())
        ));
        for c in e.candidates(&place, &user) {
            let opt = |s: &Option<String>| s.as_ref().map(|d| json::string(d)).unwrap_or_else(|| "null".into());
            out(format!(
                r#"{{"kind":"candidate","label":{},"class":"{}","detail":{},"doc":{}}}"#,
                json::string(&c.label),
                c.class,
                opt(&c.detail),
                opt(&c.doc)
            ));
        }
    }
    out(r#"{"kind":"done","phase":"complete"}"#.to_string());
}

/// The index (§15.5): each name in the file being checked, then each
/// keyword, comment, string and number in it.
/// The description of the declaration whose name starts at byte `at`: the
/// run of `#` comment lines directly above its line, without the `#` and one
/// space (D128).
pub(crate) fn doc_comment(text: &str, at: usize) -> Option<String> {
    let start = text[..at.min(text.len())].rfind('\n').map_or(0, |i| i + 1);
    let mut lines = Vec::new();
    let mut end = start;
    while end > 0 {
        let prev = text[..end - 1].rfind('\n').map_or(0, |i| i + 1);
        let line = text[prev..end - 1].trim();
        let Some(rest) = line.strip_prefix('#') else { break };
        lines.push(rest.strip_prefix(' ').unwrap_or(rest).trim_end().to_string());
        end = prev;
    }
    lines.reverse();
    let doc = lines.join("\n");
    (!doc.trim().is_empty()).then_some(doc)
}

/// The names of the index of `modules`, each at its own path.
fn emit_index_all(e: &elab::Elab, user: &str, out: &mut dyn FnMut(String)) {
    let main = e.paths.get(user).cloned().unwrap_or_default();
    emit_names(e, user, &main, out);
}

fn emit_index(e: &elab::Elab, user: &str, main: &std::path::Path, out: &mut dyn FnMut(String)) {
    emit_names(e, user, main, out);
    if let Some(f) = e.sources.get(user) {
        emit_tokens(main, f, out);
    }
}

fn emit_names(e: &elab::Elab, user: &str, main: &std::path::Path, out: &mut dyn FnMut(String)) {
    let path_of = |m: &str| -> std::path::PathBuf {
        if m == user {
            main.to_path_buf()
        } else {
            e.paths.get(m).cloned().unwrap_or_else(|| std::path::PathBuf::from(m))
        }
    };
    let pos = |m: &str, span: source::Span| -> Option<String> {
        let f = e.sources.get(m)?;
        let (sl, sc) = f.line_byte(span.start);
        let (el, ec) = f.line_byte(span.end);
        Some(format!(r#""start":[{sl},{sc}],"end":[{el},{ec}]"#))
    };
    // The names doc comments' links name (D161): occurrences too.
    let mut modules: Vec<String> = match &e.index_all {
        Some(all) => all.iter().cloned().collect(),
        None => vec![user.to_string()],
    };
    modules.sort();
    let mut links = Vec::new();
    for m in &modules {
        let Some(f) = e.sources.get(m) else { continue };
        let (module, _) = syntax::parse_module(&f.text);
        for region in literate::regions(&f.text, &module) {
            for r in literate::scan(&region).1 {
                for (span, t) in literate::link_targets(e, m, &r) {
                    links.push(elab::index::NameUse { module: m.clone(), span, what: elab::index::Use::Global(t) });
                }
            }
        }
    }
    let mut done = std::collections::HashSet::new();
    for u in e.index.iter().chain(links.iter()) {
        if !done.insert((u.module.clone(), u.span.start, u.span.end)) {
            continue;
        }
        let Some(at) = pos(&u.module, u.span) else { continue };
        let def = match e.def_of(&u.what) {
            Some((m, span)) => match pos(&m, span) {
                Some(p) => format!(r#"{{"path":{},{p}}}"#, json::string(&path_of(&m).to_string_lossy())),
                None => "null".into(),
            },
            None => "null".into(),
        };
        let doc = match e.def_of(&u.what) {
            Some((m, span)) if !matches!(u.what, elab::index::Use::Local { .. } | elab::index::Use::Module(_)) => {
                e.sources.get(&m).and_then(|f| doc_comment(&f.text, span.start as usize))
            }
            _ => None,
        };
        let type_def = match e.type_def_of(&u.what) {
            Some((m, span)) => match pos(&m, span) {
                Some(p) => format!(r#"{{"path":{},{p}}}"#, json::string(&path_of(&m).to_string_lossy())),
                None => "null".into(),
            },
            None => "null".into(),
        };
        out(format!(
            r#"{{"kind":"name","path":{},{at},"class":"{}","def":{def},"type_def":{type_def},"renamable":{},"hover":{},"doc":{}}}"#,
            json::string(&path_of(&u.module).to_string_lossy()),
            e.class_of(&u.what),
            e.renamable(&u.what, &|m: &str| m == user || e.index_all.as_ref().is_some_and(|a| a.contains(m))),
            json::string(&e.hover_of(&u.what)),
            doc.map(|d| json::string(&d)).unwrap_or_else(|| "null".into()),
        ));
    }
}

/// The keywords, comments, strings and numbers of a file (§15.5).
fn emit_tokens(path: &std::path::Path, f: &SourceFile, out: &mut dyn FnMut(String)) {
    use syntax::token::Tok;
    let (toks, comments) = syntax::lexer::tokens_and_comments(&f.text);
    let mut all: Vec<(source::Span, &str)> = toks
        .iter()
        .filter_map(|(t, span)| {
            let class = match t {
                Tok::Kw(_) => "keyword",
                Tok::Int(_) => "number",
                Tok::Byte(_) | Tok::Char(_) | Tok::Str(_) | Tok::Bytes(_) => "string",
                _ => return None,
            };
            Some((*span, class))
        })
        .collect();
    all.extend(comments.iter().map(|s| (*s, "comment")));
    all.sort_by_key(|(s, _)| s.start);
    let p = json::string(&path.to_string_lossy());
    for (span, class) in all {
        let (sl, sc) = f.line_byte(span.start);
        let (el, ec) = f.line_byte(span.end);
        out(format!(r#"{{"kind":"token","path":{p},"start":[{sl},{sc}],"end":[{el},{ec}],"class":"{class}"}}"#));
    }
}

/// The diagnostics of `c` not yet written, as JSON lines of `phase`.
fn emit_new(
    c: &Checked,
    e: Option<&elab::Elab>,
    main: &std::path::Path,
    phase: &str,
    seen: &mut std::collections::HashMap<String, usize>,
    out: &mut dyn FnMut(String),
) {
    let mut files: Vec<(String, std::path::PathBuf, &SourceFile, &[Diagnostic])> = Vec::new();
    for (m, f, ds) in &c.others {
        let path = e.and_then(|e| e.paths.get(m)).cloned().unwrap_or_else(|| std::path::PathBuf::from(&f.name));
        files.push((m.clone(), path, f, ds));
    }
    files.push((String::new(), main.to_path_buf(), &c.file, &c.diags));
    for (key, path, f, ds) in files {
        let from = seen.get(&key).copied().unwrap_or(0);
        for d in ds.iter().skip(from) {
            out(diagnostic_json(phase, &path, f, d));
        }
        seen.insert(key, ds.len());
    }
    let from = seen.get("\0internal").copied().unwrap_or(0);
    for m in c.internal.iter().skip(from) {
        let d = Diagnostic::error("internal", m.trim_end().to_string(), source::Span::new(0, 0));
        out(diagnostic_json(phase, main, &c.file, &d));
    }
    seen.insert("\0internal".into(), c.internal.len());
}

fn diagnostic_json(phase: &str, path: &std::path::Path, f: &SourceFile, d: &Diagnostic) -> String {
    let (sl, sc) = f.line_byte(d.span.start);
    let (el, ec) = f.line_byte(d.span.end);
    let notes: Vec<String> = d.notes.iter().map(|n| json::string(n)).collect();
    format!(
        r#"{{"kind":"diagnostic","phase":"{phase}","path":{},"start":[{sl},{sc}],"end":[{el},{ec}],"severity":"{}","code":"{}","message":{},"label":{},"notes":[{}],"help":{}}}"#,
        json::string(&path.to_string_lossy()),
        if d.is_error() { "error" } else { "warning" },
        d.code,
        json::string(&d.message),
        json::opt(d.label.as_deref()),
        notes.join(","),
        json::opt(d.help.as_deref()),
    )
}

/// Stage the program (§8.9): report where compile-time evaluation fails, and
/// keep the module's staged code for `checkers stage`.
fn stage_module(c: &mut Checked, e: &elab::Elab, user: &str) {
    if c.errors() > 0 {
        return;
    }
    let (staged, errs) = stage::stage_program(&e.g);
    for (d, why) in errs {
        let info = &e.g.defs[d.0 as usize];
        if *info.module != *user {
            continue;
        }
        let span = e.fn_meta.get(&d).map(|m| m.span).unwrap_or_default();
        let dg = diag::Diagnostic::error("E0273", format!("compile-time evaluation failed in `{}`", info.name), span).with_note(why);
        route(c, e, user, user, dg);
    }
    let names: Vec<String> = staged.extra.iter().map(|x| x.0.clone()).collect();
    for (k, info) in e.g.defs.iter().enumerate() {
        if let (true, Some(t)) = (*info.module == *user, staged.bodies.get(&core::DefId(k as u32))) {
            c.staged += &stage::show_def(&e.g, &info.name, t, &names);
            c.staged += "\n";
        }
    }
    for (name, t) in &staged.extra {
        c.staged += &stage::show_def(&e.g, name, t, &names);
        c.staged += "\n";
    }
    trusted_builtins(c, e, user, &staged);
}

/// Add the builtins the program relies on to the trust ledger: those reachable
/// from `main`, or from every function of the program if it has none (§16.3).
fn trusted_builtins(c: &mut Checked, e: &elab::Elab, user: &str, staged: &stage::Staged) {
    let mut progs: Vec<String> = e.user_modules.iter().filter(|m| e.package_of(m) == ".").cloned().collect();
    progs.push(user.to_string());
    let main = e.g.defs.iter().position(|d| *d.module == *user && &*d.name == "main");
    let roots: Vec<u32> = match main {
        Some(m) => vec![m as u32],
        None => (0..e.g.defs.len() as u32)
            .filter(|d| progs.iter().any(|m| **m == *e.g.defs[*d as usize].module) && e.fn_meta.contains_key(&core::DefId(*d)))
            .collect(),
    };
    let mut p = native::lower::Program::new(&e.g, Some(staged));
    native::lower::Lowerer::new(&e.g, Some(staged), &mut p).add_defs(&roots);
    let mut lines: Vec<(String, String)> = Vec::new();
    for (d, shape) in &p.defs {
        if !matches!(shape, native::lower::DefShape::Builtin { .. }) {
            continue;
        }
        let info = &e.g.defs[*d as usize];
        let at = match (e.sources.get(&*info.module), e.fn_meta.get(&core::DefId(*d))) {
            (Some(f), Some(m)) => {
                let (line, col) = f.line_col(m.span.start);
                format!("{}:{line}:{col}", f.name)
            }
            _ => info.module.to_string(),
        };
        let full = format!("{}.{}", info.module, info.name);
        lines.push((full.clone(), format!("{at}  {:<8} {full}\n", "builtin")));
    }
    lines.sort();
    let text: String = lines.into_iter().map(|l| l.1).collect();
    // Before the solver line.
    let k = c.ledger.find("solver: ").unwrap_or(c.ledger.len());
    c.ledger.insert_str(k, &text);
}

/// Check and prove the standard library itself (its lemmas and postconditions).
/// Returns the rendered errors; empty when it all verifies.
pub fn check_stdlib() -> String {
    let mut e = elab::Elab::new();
    let modules = elab::stdlib::modules();
    for m in &modules {
        e.load_stdlib(m);
    }
    let mut out = String::new();
    for (m, d) in &e.diags {
        if let Some(f) = e.sources.get(m) {
            let mut d = d.clone();
            d.span = e.real_span(m, d.span);
            e.name_globals(m, &mut d);
            out += &d.render(f);
        }
    }
    if !out.is_empty() {
        return out;
    }
    for m in &modules {
        let mut v = verify::verify(&e, m);
        for d in &mut v.diags {
            d.span = e.real_span(m, d.span);
            e.name_globals(m, d);
        }
        if let Some(f) = e.sources.get(m) {
            out += &diag::render_all(f, &v.diags);
        }
    }
    out
}

/// The modules whose code is checked: the standard-library modules the
/// program loads and its dependencies' (D109), sorted; then its own imported
/// modules, and this one.
fn program_modules(e: &elab::Elab, user: &str) -> Vec<String> {
    let mut v = std_modules(e);
    let mut deps: Vec<String> = e.user_modules.iter().filter(|m| e.package_of(m) != ".").cloned().collect();
    deps.sort();
    v.extend(deps);
    v.extend(e.user_modules.iter().filter(|m| e.package_of(m) == ".").cloned());
    // A standard-library file checked by itself is among them already (D145).
    if !v.iter().any(|m| m == user) {
        v.push(user.to_string());
    }
    v
}

/// The standard-library modules loaded, sorted.
fn std_modules(e: &elab::Elab) -> Vec<String> {
    let mut v: Vec<String> = e.modules.keys().filter(|m| m.starts_with("std.")).cloned().collect();
    v.sort();
    v
}

/// File a diagnostic of module `m` where it belongs.
fn route(c: &mut Checked, e: &elab::Elab, user: &str, m: &str, mut d: Diagnostic) {
    d.span = e.real_span(m, d.span);
    e.name_globals(m, &mut d);
    if m == user {
        c.diags.push(d);
    } else if e.sources.contains_key(m) {
        // Imported program modules and standard-library modules alike (D104).
        match c.others.iter_mut().find(|o| o.0 == m) {
            Some(o) => o.2.push(d),
            None => {
                let f = e.sources.get(m).map(|f| SourceFile::new(f.name.clone(), f.text.clone())).unwrap_or_else(|| SourceFile::new(m, ""));
                c.others.push((m.to_string(), f, vec![d]));
            }
        }
    } else {
        c.internal.push(format!("internal error (module `{m}`, which has no source): {}\n", d.message));
    }
}

/// Each module's key (D143): its name and text, the text of every program
/// or dependency module it depends on, directly or through others (the
/// modules it imports and those of the instances its checking chose, #272),
/// the standard library's text (all of it: its modules give one another, and
/// every module, the well-known types), the Z3 release and the `ckc`
/// executable. None for a module without its text, or depending on one.
fn module_keys(e: &elab::Elab) -> std::collections::HashMap<String, String> {
    use std::collections::{BTreeSet, HashMap};
    let exe = std::env::current_exe()
        .and_then(std::fs::metadata)
        .map(|m| format!("{} {:?}", m.len(), m.modified().ok()))
        .unwrap_or_default();
    let mut std_text = String::new();
    for m in std_modules(e) {
        if let Some(f) = e.sources.get(&m) {
            std_text += &format!("module {m} {}\n{}\n", f.text.len(), f.text);
        }
    }
    let tool = format!("ckc {} {exe} z3 {} std {}", env!("CARGO_PKG_VERSION"), verify::z3_version().unwrap_or_default(), verify::digest(&std_text));
    // Each module's text, hashed once; the standard library's is in `tool`.
    let texts: HashMap<&str, String> =
        e.modules.keys().filter(|m| !m.starts_with("std.")).filter_map(|m| Some((m.as_str(), verify::digest(&e.sources.get(m)?.text)))).collect();
    let edges = |m: &str| {
        let imports = e.module_deps.get(m).into_iter().flatten();
        let instances = e.instance_deps.get(m).into_iter().flatten();
        imports.chain(instances).filter(|d| !d.starts_with("std.")).cloned().collect::<Vec<String>>()
    };
    let mut keys = HashMap::new();
    'modules: for m in e.modules.keys() {
        let Some(text) = e.sources.get(m) else { continue };
        // Everything it depends on; a cycle through instances is fine.
        let mut seen = BTreeSet::new();
        let mut todo = edges(m);
        while let Some(d) = todo.pop() {
            if d != *m && seen.insert(d.clone()) {
                todo.extend(edges(&d));
            }
        }
        let mut input = format!("{tool}\nmodule {m}\n");
        for d in &seen {
            let Some(k) = texts.get(d.as_str()) else { continue 'modules };
            input += &format!("uses {d} {k}\n");
        }
        input += &text.text;
        keys.insert(m.clone(), verify::digest(&input));
    }
    keys
}

/// The program's modules verified before (D143), with their keys.
/// Modules this process has verified, by key: a doc comment's code block
/// imports the module it is in, and the standard library, all just verified
/// (D148 k).
static VERIFIED: std::sync::Mutex<Option<std::collections::HashMap<String, verify::Remembered>>> = std::sync::Mutex::new(None);

fn remembered<'a>(c: &'a mut Checked, e: &elab::Elab, user: &str) -> &'a std::collections::HashMap<String, (String, verify::Remembered)> {
    if c.remembered.is_none() {
        let mut found = std::collections::HashMap::new();
        let keys = module_keys(e);
        let memo = VERIFIED.lock().unwrap_or_else(|p| p.into_inner());
        for m in program_modules(e, user) {
            if let Some(k) = keys.get(&m) {
                let r = memo.as_ref().and_then(|x| x.get(k).cloned());
                let r = if r.is_some() || verify::modules_dir().is_none() { r } else { verify::remembered(k) };
                if let Some(r) = r {
                    found.insert(m, (k.clone(), r));
                }
            }
        }
        c.remembered = Some(found);
    }
    c.remembered.as_ref().unwrap()
}

fn prove(c: &mut Checked, e: &elab::Elab, user: &str) {
    let known = remembered(c, e, user).clone();
    let keys = module_keys(e);
    let mut ledger = String::new();
    let (mut asked, mut reused) = (0, 0);
    let mut fresh: Vec<(String, verify::Verified)> = Vec::new();
    let all = program_modules(e, user);
    for m in &all {
        let m = m.clone();
        // Verified before, with nothing it depends on changed: what it gave then.
        let v = match known.get(&m) {
            Some((_, r)) => verify::Verified {
                diags: r.warnings.clone(),
                ledger: r.ledger.clone(),
                z3_version: r.z3_version.clone(),
                proved: r.proved,
                asked: 0,
                reused: 0,
            },
            None => {
                let v = verify::verify(e, &m);
                let warnings = v.diags.iter().filter(|d| d.code == "W022").cloned().collect();
                fresh.push((m.clone(), verify::Verified { diags: warnings, ledger: v.ledger.clone(), z3_version: v.z3_version.clone(), proved: v.proved, asked: 0, reused: 0 }));
                v
            }
        };
        // The standard library and dependencies are summarized (D110, D111).
        let own = e.package_of(&m) == ".";
        if own {
            c.proved += v.proved;
        }
        asked += v.asked;
        reused += v.reused;
        let mut v = v;
        for l in &mut v.ledger {
            l.span = e.real_span(&m, l.span);
        }
        if let Some(f) = e.sources.get(&m) {
            ledger += &if own { verify::ledger_text(f, &v) } else { verify::ledger_summary(f, &v) };
        }
        for d in v.diags {
            route(c, e, user, &m, d);
        }
    }
    // One solver line at the end.
    let solver: Vec<&str> = ledger.lines().filter(|l| l.starts_with("solver: ")).collect();
    let last = solver.last().map(|s| s.to_string());
    let mut out: String = ledger.lines().filter(|l| !l.starts_with("solver: ")).map(|l| format!("{l}\n")).collect();
    if let Some(s) = last {
        out += &s;
        out.push('\n');
    }
    if reused > 0 {
        out += &format!("cache: {reused} of {asked} Z3 answers reused\n");
    }
    if !known.is_empty() && verify::modules_dir().is_some() {
        out += &format!("cache: {} of {} modules verified before\n", known.len(), all.len());
    }
    c.ledger = out;
    // Remembered only from a check with no errors at all (D143 c).
    if c.errors() == 0 {
        for (m, v) in &fresh {
            if let Some(k) = keys.get(m) {
                if verify::modules_dir().is_some() {
                    verify::remember(k, v);
                }
                let r = verify::Remembered { ledger: v.ledger.clone(), proved: v.proved, z3_version: v.z3_version.clone(), warnings: v.diags.clone() };
                VERIFIED.lock().unwrap_or_else(|p| p.into_inner()).get_or_insert_with(Default::default).insert(k.clone(), r);
            }
        }
    }
}

/// Parse, lint and type-check; also returns the elaborator and the module name.
fn elaborate(name: &str, text: &str, dir: &std::path::Path) -> (Checked, Option<(elab::Elab, String)>) {
    let mut c = parse_only(name, text);
    // Every declaration the parser recovered is checked (D122).
    let stem = std::path::Path::new(name).file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let mut e = elab::check_module(&stem, &c.file, &c.module, Some(dir));
    let user = c.module.name.as_ref().map(|q| q.dotted()).unwrap_or(stem);
    for (m, d) in &e.diags {
        route(&mut c, &e, &user, m, d.clone());
    }
    let syntax: Vec<(String, source::Span)> = c.diags.iter().filter(|d| d.is_error()).map(|d| (user.clone(), d.span)).collect();
    e.set_aside_broken(&syntax);
    // Unused code (D144): only when everything resolved, or a name that
    // failed to would look unused.
    if c.errors() == 0 {
        let mut own: Vec<String> = e.user_modules.iter().filter(|m| e.package_of(m) == ".").cloned().collect();
        own.push(user.clone());
        let u = e.unused(&user, &own);
        for (m, d) in u.warnings {
            route(&mut c, &e, &user, &m, d);
        }
        e.dead = u.dead;
    } else {
        // A branch near an error may look unreachable for want of what failed.
        e.probes.clear();
    }
    c.obligations = e.obligations.iter().filter(|o| o.module == user).count();
    (c, Some((e, user)))
}

/// The line a JSON line's `"start":[line,col]` gives.
fn start_line(l: &str) -> Option<usize> {
    let k = l.find(r#""start":["#)? + 9;
    l[k..].split(',').next()?.parse().ok()
}

/// A JSON line about a doc comment's code block (whose path is `from`), at
/// the block's place in `file` (path `to`); `None` for a line about the
/// `module` line the block was given.
fn remap_json(l: &str, from: &str, to: &str, file: &SourceFile, s: &literate::Sample) -> Option<String> {
    if s.given.iter().any(|g| l.contains(&format!("{from},\"start\":[{g},"))) {
        return None;
    }
    let mut rest = l;
    let mut done = String::new();
    while let Some(k) = rest.find(from) {
        done.push_str(&rest[..k]);
        done.push_str(to);
        rest = &rest[k + from.len()..];
        // `,"start":[l,c],"end":[l,c]` after the path: moved to the file.
        for key in [r#","start":["#, r#","end":["#] {
            let Some(t) = rest.strip_prefix(key) else { break };
            let Some(close) = t.find(']') else { break };
            let nums: Vec<usize> = t[..close].split(',').filter_map(|x| x.parse().ok()).collect();
            let [line, col] = nums[..] else { break };
            let (fl, fc) = file.line_byte(s.place_at(line, col) as u32);
            done.push_str(&format!("{key}{fl},{fc}]"));
            rest = &t[close + 1..];
        }
    }
    done.push_str(rest);
    Some(done)
}

/// The index of a doc comment's code block, at its place in `file` (D148 f).
fn emit_sample_index(file: &SourceFile, s: &literate::Sample, dir: &std::path::Path, main: &std::path::Path, out: &mut dyn FnMut(String)) {
    let name = format!("{}.ck", s.name);
    let marker = std::path::PathBuf::from(format!("/\u{1}doc/{name}"));
    let (_, e) = elaborate(&name, &s.text, dir);
    let Some((e, user)) = e else { return };
    let from = json::string(&marker.to_string_lossy());
    let to = json::string(&main.to_string_lossy());
    let mut remap = |l: String| {
        if let Some(x) = remap_json(&l, &from, &to, file, s) {
            out(x)
        }
    };
    emit_index(&e, &user, &marker, &mut remap);
}

/// Completion in a doc comment (D148 f): in a code block, as in code; after
/// `[` in its text, the names a link can name. `false` if `at` is in none.
fn complete_in_doc(name: &str, file: &SourceFile, dir: &std::path::Path, main: &std::path::Path, at: usize, out: &mut dyn FnMut(String)) -> bool {
    let (module, _) = syntax::parse_module(&file.text);
    let to = json::string(&main.to_string_lossy());
    let root = module.name.as_ref().map(|q| elab::program_root(dir, &q.dotted())).unwrap_or_else(|| dir.to_path_buf());
    let dir = root.as_path();
    for region in literate::regions(&file.text, &module) {
        let Some(line) = region.iter().find(|l| l.at <= at && at <= l.at + l.text.len()) else { continue };
        let (blocks, _) = literate::scan(&region);
        for (k, b) in blocks.iter().enumerate() {
            if !literate::is_checkers(&b.info) || !b.lines.iter().any(|l| l.at == line.at) {
                continue;
            }
            let s = literate::sample(b, k + 1, literate::Own::of(&module).as_ref());
            let Some(j) = s.starts.iter().rposition(|start| *start <= at) else { return false };
            let sname = format!("{}.ck", s.name);
            let from = json::string(&overlay::absolute(std::path::Path::new(&sname)).to_string_lossy());
            let mut remap = |l: String| {
                if let Some(x) = remap_json(&l, &from, &to, file, &s) {
                    out(x)
                }
            };
            complete_json(&sname, &s.text.clone(), dir, j, at - s.starts[j], &mut remap);
            return true;
        }
        // After `[` on this line: a link's name so far.
        let before = &line.text[..at - line.at];
        let Some(open) = before.rfind('[') else { return false };
        let typed = before[open + 1..].trim_start_matches('`');
        if !typed.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.') {
            return false;
        }
        let stem = std::path::Path::new(name).file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
        let e = elab::check_module(&stem, file, &module, Some(dir));
        let user = module.name.as_ref().map(|q| q.dotted()).unwrap_or(stem);
        let (l, c) = file.line_byte((at - typed.len()) as u32);
        let (el, ec) = file.line_byte(at as u32);
        out(format!(r#"{{"kind":"complete","path":{to},"start":[{l},{c}],"end":[{el},{ec}]}}"#));
        for (label, class) in literate::link_names(&e, &user) {
            out(format!(r#"{{"kind":"candidate","label":{},"class":"{class}","detail":null,"doc":null}}"#, json::string(&label)));
        }
        out(r#"{"kind":"done","phase":"complete"}"#.to_string());
        return true;
    }
    false
}

/// The doc comments' links and code (D148 e): W030–W033.
fn doc_comments(c: &mut Checked, e: &elab::Elab, user: &str, dir: &std::path::Path) {
    let (diags, samples) = literate::links_and_samples(&c.file.text, &c.module, e, user);
    c.diags.extend(diags);
    // A sample is a module of the program its module is in (D148 d).
    let root = e.base_dir.clone().unwrap_or_else(|| dir.to_path_buf());
    for s in &samples {
        c.diags.extend(literate::sample_diagnostics(s, &root));
    }
}

/// Evaluate the module's `check` declarations (D40).
fn run_checks(c: &mut Checked, e: &elab::Elab, user: &str) {
    // A module verified before has passed its `check`s (D143).
    let known: std::collections::HashSet<String> = remembered(c, e, user).keys().cloned().collect();
    let mods: Vec<String> = program_modules(e, user).into_iter().filter(|m| !known.contains(m)).collect();
    if !e.checks.iter().any(|(m, _, _)| mods.contains(m)) {
        return;
    }
    // Native code (D80): one in-memory module for all of this program's checks.
    let mut ev = native::eval::Evaluator::new(&e.g);
    for (m, span, t) in &e.checks {
        if !mods.contains(m) {
            continue;
        }
        match ev.eval(t) {
            Ok(v) if ev.is_false(v) => {
                let mut d = diag::Diagnostic::error("E0260", "this `check` is false", *span).with_label("evaluates to `False`");
                if let core::Tm::PrimApp(core::Prim::Eq, sides) = t {
                    if let [l, r] = sides.as_slice() {
                        if let (Ok(lv), Ok(rv)) = (ev.eval(l), ev.eval(r)) {
                            let ty = e.check_eq_tys.get(span);
                            d = d
                                .with_note(format!("left side:  `{}`", ev.show_as(lv, ty)))
                                .with_note(format!("right side: `{}`", ev.show_as(rv, ty)));
                            ev.release(lv);
                            ev.release(rv);
                        }
                    }
                }
                route(c, e, user, m, d);
            }
            Ok(v) => ev.release(v),
            Err(err) => route(
                c,
                e,
                user,
                m,
                diag::Diagnostic::error("E0261", "this `check` stopped with a runtime error", *span)
                    .with_label("evaluating this failed")
                    .with_note(err),
            ),
        }
    }
}

/// The outcome of `run`.
pub struct Ran {
    /// Diagnostics (empty when there are none).
    pub report: String,
    /// Process exit code: the program's, 2 if it didn't type-check, 70 after a runtime error.
    pub code: u8,
}

/// Check and prove `text`, then call its exported `main` with `args` (D43,
/// §13.4), as native code (§14). The program writes to this process's
/// standard streams, so the report is printed to standard error before it
/// runs; the returned report is empty. Imported modules are looked up in
/// `dir`; `threads`: threads for behaviours and `par` (1: the deterministic
/// FIFO scheduler, D67).
pub fn run(name: &str, text: &str, dir: &std::path::Path, args: &[String], threads: usize) -> Ran {
    let (e, main, staged, report) = match ready_to_run(name, text, dir) {
        Ok(r) => r,
        Err(ran) => return ran,
    };
    eprint!("{report}");
    let code = native::run(&e.g, Some(&staged), main, args, threads);
    Ran { report: String::new(), code: code as u8 }
}

/// `checkers build`: check and prove, then write an executable.
pub fn build(name: &str, text: &str, dir: &std::path::Path, out: &std::path::Path, release: bool) -> Ran {
    let (e, main, staged, mut report) = match ready_to_run(name, text, dir) {
        Ok(r) => r,
        Err(ran) => return ran,
    };
    // A release build relies on no `admit` anywhere in the program, its
    // dependencies or the standard library (§7.4, D116); axioms stay allowed.
    if release && !e.admits.is_empty() {
        let mut admits: Vec<&elab::Trusted> = e.admits.iter().collect();
        admits.sort_by(|a, b| (a.module.as_str(), a.span.start).cmp(&(b.module.as_str(), b.span.start)));
        for a in &admits {
            let d = Diagnostic::error("E0455", "a release build can't rely on an `admit`", a.span)
                .with_label(format!("assumed, not proven: {}", a.what.trim_start_matches("admit: ")))
                .with_help("prove it, or build without `--release`");
            report += &match e.sources.get(&a.module) {
                Some(f) => d.render(f),
                None => format!("error[E0455]: a release build can't rely on an `admit` ({}: {})\n", a.module, a.what),
            };
            report.push('\n');
        }
        report += &format!("error: `--release` refuses this program: it relies on {} `admit`{}\n", admits.len(), if admits.len() == 1 { "" } else { "s" });
        return Ran { report, code: 1 };
    }
    match native::build(&e.g, Some(&staged), main, out) {
        Ok(()) => Ran { report, code: 0 },
        Err(msg) => {
            report += &format!("error: {msg}\n");
            Ran { report, code: 2 }
        }
    }
}

/// Check, prove and stage a program for running: the elaborated program,
/// `main`, the staged code, and the report so far (warnings). A program
/// with any error doesn't run (§7.4).
fn ready_to_run(name: &str, text: &str, dir: &std::path::Path) -> Result<(elab::Elab, core::DefId, stage::Staged, String), Ran> {
    let (mut c, e) = elaborate(name, text, dir);
    let Some((mut e, user)) = e else { return Err(Ran { report: c.report(), code: 2 }) };
    run_checks(&mut c, &e, &user);
    prove(&mut c, &e, &user);
    let report = if c.all_diags().next().is_none() && c.internal.is_empty() { String::new() } else { c.report() };
    if c.errors() > 0 || !c.internal.is_empty() {
        return Err(Ran { report, code: 2 });
    }
    let exported = e.modules.get(&user).is_some_and(|m| m.exported_values.contains("main"));
    let main = e.g.defs.iter().position(|d| *d.module == user && &*d.name == "main");
    let (Some(main), true) = (main, exported) else {
        return Err(Ran { report: format!("{report}error: `{}` has no exported `main` function\n", c.file.name), code: 2 });
    };
    // Staging is compile-time evaluation: it keeps its checks (§13.3).
    let (staged, _) = stage::stage_program(&e.g);
    // Every obligation is proved. Unless a fact the proofs use may be an
    // `admit`'s, assumed (§13.3), native code relies on them: the bounds
    // signatures give, and no checks of guarded operations.
    if e.admits.is_empty() {
        e.g.bounds = std::mem::take(&mut e.bounds);
        e.g.proved = true;
    }
    Ok((e, core::DefId(main as u32), staged, report))
}

/// Run `f` on a thread with a large stack: checking recurses deeply (long
/// lists in types, deep terms).
pub fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("spawn the checking thread")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e))
}
