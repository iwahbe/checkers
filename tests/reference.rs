//! The site's Reference lists every diagnostic the compiler and the tools
//! report, and nothing else (SPEC D166 c): each code written as a string in
//! `src/` or `tools/` has a row in `site/reference/diagnostics.md`.

use std::collections::BTreeSet;
use std::path::Path;

/// Codes written as string literals: `"E0450"`, `"W032"`.
fn codes_in(text: &str, out: &mut BTreeSet<String>) {
    let b = text.as_bytes();
    let mut i = 0;
    while i + 6 <= b.len() {
        if b[i] == b'"' && (b[i + 1] == b'E' || b[i + 1] == b'W') {
            let digits = b[i + 2..].iter().take_while(|c| c.is_ascii_digit()).count();
            let want = if b[i + 1] == b'E' { 4 } else { 3 };
            if digits == want && b.get(i + 2 + digits) == Some(&b'"') {
                out.insert(String::from_utf8_lossy(&b[i + 1..i + 2 + digits]).into_owned());
            }
        }
        i += 1;
    }
}

fn walk(dir: &Path, ext: &str, out: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            walk(&path, ext, out);
        } else if path.extension().is_some_and(|e| e == ext) {
            codes_in(&std::fs::read_to_string(&path).unwrap(), out);
        }
    }
}

#[test]
fn every_diagnostic_is_in_the_reference() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut used = BTreeSet::new();
    walk(&root.join("src"), "rs", &mut used);
    walk(&root.join("tools"), "ck", &mut used);
    let page = std::fs::read_to_string(root.join("site/reference/diagnostics.md")).unwrap();
    let mut listed = BTreeSet::new();
    for line in page.lines().filter(|l| l.starts_with("| `")) {
        let code = line.trim_start_matches("| `").split('`').next().unwrap_or("");
        listed.insert(code.to_string());
    }
    let missing: Vec<_> = used.difference(&listed).collect();
    let stale: Vec<_> = listed.difference(&used).collect();
    assert!(missing.is_empty(), "codes the compiler reports but site/reference/diagnostics.md doesn't list: {missing:?}");
    assert!(stale.is_empty(), "codes site/reference/diagnostics.md lists but nothing reports: {stale:?}");
}
