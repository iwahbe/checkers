//! Unsaved files (§15.5, D120): `ckc check --overlay FILE` gives text that
//! stands in for files on disk. Every source file the compiler reads goes
//! through `read`, so module resolution is the same with or without it.

use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};
use std::sync::OnceLock;

static OVERLAY: OnceLock<HashMap<PathBuf, String>> = OnceLock::new();

/// Install the overlay (once, before checking). Keys are paths as given.
pub fn set(files: impl IntoIterator<Item = (String, String)>) {
    let map = files.into_iter().map(|(p, t)| (absolute(Path::new(&p)), t)).collect();
    let _ = OVERLAY.set(map);
}

/// `path` made absolute and with `.` and `..` removed, without touching the
/// disk (an unsaved file need not exist).
pub fn absolute(path: &Path) -> PathBuf {
    let base = std::path::absolute(path).unwrap_or_else(|_| path.to_path_buf());
    let mut out = PathBuf::new();
    for c in base.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            c => out.push(c),
        }
    }
    out
}

/// The text of a source file: from the overlay if it has it, else the disk.
pub fn read(path: &Path) -> std::io::Result<String> {
    if let Some(t) = OVERLAY.get().and_then(|m| m.get(&absolute(path))) {
        return Ok(t.clone());
    }
    std::fs::read_to_string(path)
}
