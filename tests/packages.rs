//! Packages (M14, SPEC §16.4, D107–D111): `checkers` in a directory with
//! `checkers.json` resolves path and git dependencies (minimal version
//! selection), keeps `checkers.lock`, and passes the packages to `ckc`.
//! Git dependencies are local repositories, so this runs offline.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

/// `checkers`, built once for these tests.
fn tool() -> &'static Path {
    static TOOL: OnceLock<PathBuf> = OnceLock::new();
    TOOL.get_or_init(|| {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let exe = std::env::temp_dir().join(format!("checkers-packages-{}-tool", std::process::id()));
        let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
            .args(["build", "tools/checkers.ck", "-o"])
            .arg(&exe)
            .current_dir(root)
            .env("CHECKERS_NO_CACHE", "1")
            .output()
            .expect("run ckc");
        assert!(out.status.success(), "building checkers: {}", String::from_utf8_lossy(&out.stderr));
        exe
    })
}

struct World {
    root: PathBuf,
}

impl World {
    fn new(name: &str) -> World {
        let root = std::env::temp_dir().join(format!("checkers-packages-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).unwrap();
        World { root }
    }

    fn write(&self, rel: &str, text: &str) {
        let p = self.root.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    fn read(&self, rel: &str) -> String {
        std::fs::read_to_string(self.root.join(rel)).unwrap_or_default()
    }

    fn git(&self, repo: &str, args: &[&str]) {
        let out = Command::new("git")
            .args(["-c", "user.email=t@example.com", "-c", "user.name=t", "-c", "init.defaultBranch=main"])
            .args(args)
            .current_dir(self.root.join(repo))
            .output()
            .expect("run git");
        assert!(out.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    }

    fn url(&self, repo: &str) -> String {
        self.root.join(repo).to_string_lossy().into_owned()
    }

    /// A git package `util`: tag v`version`, with `count.ck` as given.
    fn release_util(&self, version: &str, count: &str) {
        if !self.root.join("util/.git").exists() {
            std::fs::create_dir_all(self.root.join("util")).unwrap();
            self.git("util", &["init", "-q"]);
        }
        self.write("util/checkers.json", &format!("{{ \"name\": \"util\", \"version\": \"{version}\", \"toolchain\": \"0.1.0\" }}\n"));
        self.write("util/count.ck", count);
        self.git("util", &["add", "-A"]);
        self.git("util", &["commit", "-qm", version]);
        self.git("util", &["tag", &format!("v{version}")]);
    }

    fn checkers(&self, dir: &str, args: &[&str]) -> Output {
        Command::new(tool())
            .args(args)
            .current_dir(self.root.join(dir))
            .env("CKC", env!("CARGO_BIN_EXE_ckc"))
            .env("XDG_CACHE_HOME", self.root.join("cache"))
            .env("CHECKERS_NO_CACHE", "1")
            .output()
            .expect("run checkers")
    }
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// Standard error without the `fetching` lines.
fn errors(o: &Output) -> String {
    text(&o.stderr).lines().filter(|l| !l.starts_with("checkers: fetching ")).map(|l| format!("{l}\n")).collect()
}

const COUNT_1_0: &str = "module count\n\nexport fn double n -> m : n~Nat, m~Nat, m == n + n\n    n + n\n";
const COUNT_1_1: &str = "module count\n\nexport fn double n -> m : n~Nat, m~Nat, m == n + n\n    n + n\n\nexport fn triple n -> m : n~Nat, m~Nat, m == 3 * n\n    n + n + n\n";

const SHARED: &str = "module text.greet\n\nimport util.count\n\nexport fn greeting name n -> s : name~String, n~Nat, s~String\n    \"hello, \" ++ name ++ \" \" ++ format (count.double n)\n\nexport fn at_least n -> m : n~Nat, m~Nat, m >= n\n    n + 1\n";

const MAIN: &str = "module main\n\nimport std.system (System, ExitCode)\nimport std.terminal\nimport shared.text.greet\n\nexport fn main args sys -> code : args~List String, sys~System, code~ExitCode\n    let System { term } = sys\n    terminal.print_line (greet.greeting \"you\" 2) term\n    Success\n";

fn manifest(name: &str, deps: &[String]) -> String {
    format!(
        "{{\n  \"name\": \"{name}\",\n  \"version\": \"0.1.0\",\n  \"toolchain\": \"0.1.0\",\n  \"dependencies\": {{\n{}\n  }}\n}}\n",
        deps.iter().map(|d| format!("    {d}")).collect::<Vec<_>>().join(",\n")
    )
}

fn git_dep(w: &World, name: &str, version: &str) -> String {
    format!("\"{name}\": {{ \"git\": \"{}\", \"version\": \"{version}\" }}", w.url(name))
}

/// An app with a path dependency `shared`, which has a git dependency `util`.
fn app(w: &World) {
    w.release_util("1.0.0", COUNT_1_0);
    w.write("shared/checkers.json", &manifest("shared", &[git_dep(w, "util", "1.0.0")]));
    w.write("shared/text/greet.ck", SHARED);
    w.write("app/checkers.json", &manifest("app", &["\"shared\": { \"path\": \"../shared\" }".to_string()]));
    w.write("app/main.ck", MAIN);
}

#[test]
fn builds_with_git_and_path_dependencies() {
    let w = World::new("build");
    app(&w);
    let exe = w.root.join("app/app-bin");
    let out = w.checkers("app", &["build", "-o", exe.to_str().unwrap()]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert!(text(&out.stderr).contains("checkers: fetching util 1.0.0 from "), "{}", text(&out.stderr));
    let ran = Command::new(&exe).output().unwrap();
    assert_eq!(text(&ran.stdout), "hello, you 4\n");

    // The lock file pins util's commit; the path dependency as written.
    let lock = w.read("app/checkers.lock");
    assert!(lock.starts_with("{\n  \"shared\": { \"path\": \"../shared\" },\n  \"util\": { \"git\": "), "{lock}");
    assert!(lock.contains("\"version\": \"1.0.0\", \"commit\": \""), "{lock}");

    // The trust ledger lists both packages.
    let trust = w.checkers("app", &["trust"]);
    let ledger = text(&trust.stdout);
    assert!(ledger.contains("<shared>/text/greet.ck  proved   1 by smt, 0 computed\n"), "{ledger}");
    assert!(ledger.contains("<util>/count.ck  proved   1 by smt, 0 computed\n"), "{ledger}");

    // Nothing is fetched again.
    let again = w.checkers("app", &["check"]);
    assert!(again.status.success(), "{}", text(&again.stderr));
    assert_eq!(text(&again.stderr), "main.ck: 0 errors, 0 warnings\n");
}

#[test]
fn a_new_version_in_the_manifest_is_used() {
    let w = World::new("upgrade");
    app(&w);
    assert!(w.checkers("app", &["check"]).status.success());
    w.release_util("1.1.0", COUNT_1_1);
    // The app now needs util 1.1.0 itself (for `triple`); shared still asks for 1.0.0.
    w.write("app/checkers.json", &manifest("app", &["\"shared\": { \"path\": \"../shared\" }".to_string(), git_dep(&w, "util", "1.1.0")]));
    w.write("app/main.ck", &MAIN.replace("import shared.text.greet\n", "import shared.text.greet\nimport util.count\n").replace("(greet.greeting \"you\" 2)", "(greet.greeting \"you\" (count.triple 1))"));
    let out = w.checkers("app", &["run"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), "hello, you 6\n");
    assert!(w.read("app/checkers.lock").contains("\"version\": \"1.1.0\""));
}

#[test]
fn the_lock_file_pins_the_commit() {
    let w = World::new("pin");
    app(&w);
    assert!(w.checkers("app", &["check"]).status.success());
    let lock = w.read("app/checkers.lock");
    // Move the tag to a commit that breaks `double`.
    w.write("util/count.ck", "module count\n\nexport fn double n -> m : n~Nat, m~Nat\n    n\n");
    w.git("util", &["commit", "-qam", "moved"]);
    w.git("util", &["tag", "-f", "v1.0.0"]);
    let out = w.checkers("app", &["run"]);
    assert_eq!(text(&out.stdout), "hello, you 4\n", "{}", text(&out.stderr));
    assert_eq!(w.read("app/checkers.lock"), lock);
}

#[test]
fn two_major_versions_are_an_error() {
    let w = World::new("major");
    app(&w);
    w.release_util("2.0.0", COUNT_1_0);
    w.write("app/checkers.json", &manifest("app", &["\"shared\": { \"path\": \"../shared\" }".to_string(), git_dep(&w, "util", "2.0.0")]));
    let out = w.checkers("app", &["check"]);
    assert_eq!(out.status.code(), Some(1));
    let err = errors(&out);
    assert!(err.ends_with("checkers: `util` is needed at two major versions: 1.0.0 (by `shared`) and 2.0.0 (by `app`)\n"), "{err}");
}

#[test]
fn only_declared_dependencies_can_be_imported() {
    let w = World::new("undeclared");
    app(&w);
    // `app` uses util without declaring it.
    w.write("app/main.ck", &MAIN.replace("import shared.text.greet\n", "import shared.text.greet\nimport util.count\n"));
    let out = w.checkers("app", &["check"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        errors(&out),
        "error[E0227]: `util` is not a dependency of this program\n --> main.ck:6:8\n  |\n6 | import util.count\n  |        ^^^^^^^^^^ this program doesn't list `util` in its `dependencies`\n  = help: add `util` to `dependencies` in checkers.json\n\nmain.ck: 1 error, 0 warnings\n"
    );
}

#[test]
fn manifest_problems_have_a_position() {
    let w = World::new("manifest");
    app(&w);
    let cases = [
        ("\"toolchain\"", "\"toolchian\"", "checkers: checkers.json:4:3: unknown field `toolchian`: the fields are `name`, `version`, `toolchain` and `dependencies`\n"),
        ("\"version\": \"0.1.0\"", "\"version\": \"0.1\"", "checkers: checkers.json:3:3: `version` must be MAJOR.MINOR.PATCH, like 1.2.0\n"),
        ("\"name\": \"app\",", "\"name\": \"app\"", "checkers: checkers.json:3:3: unexpected `\"`\n"),
        ("\"name\": \"app\"", "\"name\": \"App\"", "checkers: checkers.json:2:3: `App` isn't a package name: lower-case letters, digits and `_`, starting with a letter; not `std`\n"),
        ("{ \"path\": \"../shared\" }", "{ \"path\": \"../shared\", \"version\": \"1.0.0\" }", "checkers: checkers.json:6:38: a path dependency has no `version`: it is used as it is\n"),
        ("\"shared\": {", "\"sharde\": {", "checkers: ../shared is the package `shared`, but `app` calls it `sharde`: a dependency's name must be its package's name\n"),
        ("\"toolchain\": \"0.1.0\"", "\"toolchain\": \"9.0.0\"", "checkers: this package needs checkers 9.0.0 or newer; this is 0.1.0\n"),
    ];
    let good = w.read("app/checkers.json");
    for (from, to, expected) in cases {
        assert!(good.contains(from), "{from}");
        w.write("app/checkers.json", &good.replacen(from, to, 1));
        let out = w.checkers("app", &["check"]);
        assert_eq!(out.status.code(), Some(1), "{to}");
        assert_eq!(errors(&out), expected, "{to}");
    }
}

fn ckc(w: &World, dir: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ckc")).args(args).current_dir(w.root.join(dir)).env("CHECKERS_NO_CACHE", "1").output().expect("run ckc")
}

#[test]
fn ckc_package_flags_and_messages() {
    let w = World::new("ckc");
    w.write("lib/a.ck", "module wrong\n");
    w.write("lib/b.ck", "module b\n\nimport lib.c\nimport nothing\n");
    w.write("prog/p.ck", "module p\n\nimport lib.a\nimport lib.b\n");
    let out = ckc(&w, "prog", &["check", "--package", "lib=../lib", "--uses", ".=lib", "p.ck"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        text(&out.stderr),
        "error[E0223]: this file must declare `module a`, its path in package `lib`\n --> <lib>/a.ck:1:8\n  |\n1 | module wrong\n  |        ^^^^^ declares `wrong`\n  = help: start the file with `module a`\n\n\
         error[E0227]: `lib` is not a dependency of package `lib`\n --> <lib>/b.ck:3:8\n  |\n3 | import lib.c\n  |        ^^^^^ package `lib` doesn't list `lib` in its `dependencies`\n  = help: a package imports its own modules by their path in it: `import c`\n\n\
         error[E0220]: unknown module `nothing`\n --> <lib>/b.ck:4:8\n  |\n4 | import nothing\n  |        ^^^^^^^ no file `nothing.ck` in package `lib`\n\n\
         p.ck: 3 errors, 0 warnings\n"
    );
    let bad = ckc(&w, "prog", &["check", "--package", "lib=../nowhere", "p.ck"]);
    assert_eq!((bad.status.code(), text(&bad.stderr)), (Some(2), "error: `--package lib=../nowhere`: no directory `../nowhere`\n".to_string()));
    let bad = ckc(&w, "prog", &["check", "--package", "lib=../lib", "--uses", ".=lib,other", "p.ck"]);
    assert_eq!((bad.status.code(), text(&bad.stderr)), (Some(2), "error: `--uses .=…` names `other`, which no `--package` gives\n".to_string()));
}
