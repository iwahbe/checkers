//! The embedded standard library (`stdlib/*.ck`).

use super::Elab;
use crate::diag::Diagnostic;
use crate::source::SourceFile;

pub const MODULES: &[(&str, &str)] = &[
    ("prelude", include_str!("../../stdlib/prelude.ck")),
    ("list", include_str!("../../stdlib/list.ck")),
    ("bag", include_str!("../../stdlib/bag.ck")),
    ("cown", include_str!("../../stdlib/cown.ck")),
    ("future", include_str!("../../stdlib/future.ck")),
    ("system", include_str!("../../stdlib/system.ck")),
    ("terminal", include_str!("../../stdlib/terminal.ck")),
    ("files", include_str!("../../stdlib/files.ck")),
    ("bytes", include_str!("../../stdlib/bytes.ck")),
    ("string", include_str!("../../stdlib/string.ck")),
    ("char", include_str!("../../stdlib/char.ck")),
    ("utf8", include_str!("../../stdlib/utf8.ck")),
    ("decimal", include_str!("../../stdlib/decimal.ck")),
    ("cursor", include_str!("../../stdlib/cursor.ck")),
    ("actor", include_str!("../../stdlib/actor.ck")),
];

pub fn source(name: &str) -> Option<&'static str> {
    MODULES.iter().find(|(n, _)| *n == name).map(|(_, s)| *s)
}

impl Elab {
    /// Load a stdlib module if it isn't loaded yet. Returns false if it doesn't exist.
    pub fn load_stdlib(&mut self, name: &str) -> bool {
        if self.modules.contains_key(name) {
            return true;
        }
        let Some(text) = source(name) else { return false };
        let file = SourceFile::new(format!("<stdlib>/{name}.ck"), text);
        let (m, diags) = crate::syntax::parse_module(text);
        for d in diags {
            self.diags.push((name.to_string(), d));
        }
        self.sources.insert(name.to_string(), file);
        let saved = std::mem::take(&mut self.cur);
        let saved_fn = self.cur_fn.take();
        let saved_calls = std::mem::take(&mut self.calls);
        let saved_mod_fns = std::mem::take(&mut self.module_fns);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.elab_module(name, &m, true);
        self.cur = saved;
        self.cur_fn = saved_fn;
        self.calls = saved_calls;
        self.module_fns = saved_mod_fns;
        self.deferred = saved_deferred;
        true
    }

    /// Load the program module `a.b` from `a/b.ck` beside the program (D53).
    /// Returns false if there is no such file.
    pub fn load_user(&mut self, name: &str, _span: crate::source::Span) -> bool {
        let Some(base) = self.base_dir.clone() else { return false };
        let rel: std::path::PathBuf = name.split('.').collect::<std::path::PathBuf>().with_extension("ck");
        let path = base.join(&rel);
        let Ok(text) = std::fs::read_to_string(&path) else { return false };
        let file = SourceFile::new(path.to_string_lossy().to_string(), text.clone());
        let (m, diags) = crate::syntax::parse_module(&text);
        let broken = diags.iter().any(|d| d.is_error());
        for d in diags {
            self.diags.push((name.to_string(), d));
        }
        for d in crate::lint::naming(&m) {
            self.diags.push((name.to_string(), d));
        }
        self.sources.insert(name.to_string(), file);
        self.user_modules.push(name.to_string());
        if broken {
            // Its errors are reported; importers see an empty module.
            self.modules.insert(name.to_string(), super::ModuleInfo { name: name.to_string(), ..Default::default() });
            return true;
        }
        match &m.name {
            Some(q) if q.dotted() == name => {}
            other => {
                let span = other.as_ref().map(|q| q.span).unwrap_or_default();
                let found = other.as_ref().map(|q| q.dotted()).unwrap_or_default();
                self.diags.push((
                    name.to_string(),
                    Diagnostic::error("E0223", format!("this file must declare `module {name}`, because it is imported as `{name}`"), span)
                        .with_label(if found.is_empty() { "no module declaration".to_string() } else { format!("declares `{found}`") })
                        .with_help(format!("start the file with `module {name}`")),
                ));
            }
        }
        let saved = std::mem::take(&mut self.cur);
        let saved_fn = self.cur_fn.take();
        let saved_calls = std::mem::take(&mut self.calls);
        let saved_mod_fns = std::mem::take(&mut self.module_fns);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.elab_module(name, &m, false);
        self.cur = saved;
        self.cur_fn = saved_fn;
        self.calls = saved_calls;
        self.module_fns = saved_mod_fns;
        self.deferred = saved_deferred;
        true
    }

    pub fn stdlib_error(&mut self, name: &str, d: Diagnostic) {
        self.diags.push((name.to_string(), d));
    }
}
