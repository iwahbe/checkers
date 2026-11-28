//! Packages (M14, SPEC §16.4, #597, #598, #594, #595, #608): `checkers` in a directory with
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

const SHARED: &str = "module text.greet\n\nimport util.count\nimport std.string (format)\n\nexport fn greeting name n -> s : name~String, n~Nat, s~String\n    format\"hello, {name} {count.double n}\"\n\nexport fn at_least n -> m : n~Nat, m~Nat, m >= n\n    n + 1\n";

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
        ("\"version\": \"0.1.0\"", "\"version\": \"0.1\"", "checkers: checkers.json:3:14: `version` must be MAJOR.MINOR.PATCH, like 1.2.0\n"),
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

#[test]
fn lock_file_versions_have_no_leading_zeros() {
    let w = World::new("lockzeros");
    app(&w);
    w.write("app/checkers.lock", "{\n  \"util\": { \"git\": \"../util\", \"version\": \"1.01.0\", \"commit\": \"0\" }\n}\n");
    let out = w.checkers("app", &["check"]);
    assert_eq!(
        (out.status.code(), errors(&out)),
        (Some(1), "checkers: checkers.lock:2:42: `version` can't have leading zeros\nhelp: write \"1.1.0\"\n".to_string())
    );
}

#[test]
fn lock_file_names_are_package_names() {
    let w = World::new("lockname");
    app(&w);
    w.write("app/checkers.lock", "{\n  \"Shared\": { \"path\": \"../shared\" }\n}\n");
    let out = w.checkers("app", &["check"]);
    assert_eq!(
        (out.status.code(), errors(&out)),
        (Some(1), "checkers: checkers.lock:2:3: `Shared` isn't a package name: lower-case letters, digits and `_`, starting with a letter; not `std`\n".to_string())
    );
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

/// A name another package declares without exporting gets a `note:`, not
/// advice to change that package; within the dependency itself, the `help:`
/// to export it is still given (SPEC §6).
#[test]
fn another_packages_private_names_get_a_note() {
    let w = World::new("private");
    w.write(
        "lib/shape.ck",
        "module shape\n\nexport abstract enum Size\n    Measured n : n~Nat\n\nexport fn size n -> s : n~Nat, s~Size\n    Measured (secret n)\n\nfn secret n -> m : n~Nat, m~Nat\n    n\n",
    );
    w.write("lib/twice.ck", "module twice\n\nimport shape\n\nexport fn twice n -> m : n~Nat, m~Nat\n    shape.secret (n + n)\n");
    w.write(
        "prog/p.ck",
        "module p\n\nimport lib.shape (Size)\nimport lib.shape\nimport lib.twice\n\nfn made_up -> s : s~Size\n    Measured 3\n\ncheck shape.secret 1 == 1\n",
    );
    let out = ckc(&w, "prog", &["check", "--package", "lib=../lib", "--uses", ".=lib", "p.ck"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        text(&out.stderr),
        "error[E0206]: module `lib.shape` has no export named `secret`\n --> <lib>/twice.ck:6:11\n  |\n6 |     shape.secret (n + n)\n  |           ^^^^^^\n  = help: `lib.shape` declares `secret` but doesn't export it; mark it `export` there to use it here\n\n\
         error[E0204]: unknown name `Measured`\n --> p.ck:8:5\n  |\n8 |     Measured 3\n  |     ^^^^^^^^ not found\n  = note: `Size` is abstract: its values come only from `lib.shape`'s functions\n\n\
         error[E0206]: module `lib.shape` has no export named `secret`\n  --> p.ck:10:13\n   |\n10 | check shape.secret 1 == 1\n   |             ^^^^^^\n   = note: `secret` is private to `lib.shape`\n\n\
         p.ck: 3 errors, 0 warnings\n"
    );
}

/// An instance of a class of several types goes in the package of the class
/// or of one of its types, with no bare variable before that type (Rust's
/// orphan rule, #145); an overlap with a dependency's instance is found here.
#[test]
fn instance_orphan_rule_by_any_type() {
    let w = World::new("orphan");
    w.write(
        "lib/hole.ck",
        "module hole\n\nexport class Hole s h\n    fn hole tag x -> r : tag~s, x~h, r~String\n\nexport class Rel s a t\n    fn rel x y z -> r : x~s, y~a, z~t, r~Bool\n\nexport record Format\n    prefix~String\n\nexport record Page\n    title~String\n\ninstance Hole Page a\n    fn hole p x\n        p.title\n",
    );
    let check = |name: &str, body: &str| {
        w.write(&format!("prog/{name}.ck"), &format!("module {name}\n\nimport lib.hole (Hole, Rel, Format, Page)\n\nrecord Mine\n    n~Int\n\n{body}"));
        let out = ckc(&w, "prog", &["check", "--package", "lib=../lib", "--uses", ".=lib", &format!("{name}.ck")]);
        (out.status.code(), text(&out.stderr))
    };
    // This package's type, after the class's and another package's.
    assert_eq!(check("later", "instance Hole Format Mine\n    fn hole f m\n        f.prefix\n"), (Some(0), "later.ck: 0 errors, 0 warnings\n".to_string()));
    // This package's type first.
    assert_eq!(check("first", "instance Hole Mine Int\n    fn hole m x\n        \"int\"\n"), (Some(0), "first.ck: 0 errors, 0 warnings\n".to_string()));
    // No type of this package.
    assert_eq!(
        check("none", "instance Hole Format Int\n    fn hole f x\n        f.prefix\n"),
        (
            Some(1),
            "error[E0282]: `instance Hole Format Int` must be in the package of `Hole` or of one of its types\n --> none.ck:8:1\n  |\n8 | instance Hole Format Int\n  | ^^^^^^^^^^^^^^^^^^^^^^^^ none of them is declared in this package\n  = help: an instance goes with its class or one of its types (Rust's orphan rule); wrap a type in a record of your own to give it this instance\n\nnone.ck: 1 error, 0 warnings\n"
                .to_string()
        )
    );
    // A bare variable before this package's type.
    assert_eq!(
        check("var_first", "instance Rel Format a Mine\n    fn rel f x m\n        True\n"),
        (
            Some(1),
            "error[E0282]: `instance Rel Format a Mine` must be in the package of `Rel` or of one of its types\n --> var_first.ck:8:21\n  |\n8 | instance Rel Format a Mine\n  |                     ^ `a` comes before `Mine`, this package's type\n  = help: an instance whose types begin with a type variable could overlap another package's; put this package's type before any variable\n\nvar_first.ck: 1 error, 0 warnings\n"
                .to_string()
        )
    );
    // Overlaps the dependency's `instance Hole Page a`: reported here.
    assert_eq!(
        check("overlap", "instance Hole Page Mine\n    fn hole p m\n        p.title\n"),
        (
            Some(1),
            "error[E0283]: `instance Hole Page Mine` overlaps another instance\n --> overlap.ck:8:1\n  |\n8 | instance Hole Page Mine\n  | ^^^^^^^^^^^^^^^^^^^^^^^ `Hole Page a` is already declared at lib.hole:15\n  = help: no two instances of a class may match the same types; make one of them for other types\n\noverlap.ck: 1 error, 0 warnings\n"
                .to_string()
        )
    );
}

#[test]
fn fetch_failures_are_reported_plainly() {
    let w = World::new("fetchfail");
    app(&w);
    // A version with no tag: only our message, nothing from git.
    w.write("shared/checkers.json", &manifest("shared", &[git_dep(&w, "util", "9.0.0")]));
    let out = w.checkers("app", &["check"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(errors(&out), format!("checkers: `util`: {} has no tag v9.0.0\n", w.url("util")));
    // A repository that isn't there: git's reason is part of the message.
    w.write("shared/checkers.json", &manifest("shared", &[format!("\"util\": {{ \"git\": \"{}/nowhere\", \"version\": \"1.0.0\" }}", w.root.display())]));
    let out = w.checkers("app", &["check"]);
    assert_eq!(out.status.code(), Some(1));
    let err = errors(&out);
    assert!(err.starts_with(&format!("checkers: could not fetch `util` from {}/nowhere: fatal: ", w.root.display())), "{err}");
    assert_eq!(err.lines().count(), 1, "{err}");
}

/// A runtime error in another package's private function names the function
/// of that package the program called, however deep (SPEC §6 rule 9): the
/// private `walk`, reached from `at`, from `first`, and through `list.map`
/// from `every`, is named after each, whether or not `list.map` is
/// specialized for the function `every` passes it.
#[test]
fn a_runtime_error_names_the_function_the_program_called() {
    let w = World::new("runtime");
    w.write(
        "lib/pick.ck",
        "module pick\n\nimport std.list\n\n\
         export fn at xs i -> x : xs~Array Int, i~Nat, i < len xs, x~Int\n    element xs i\n\n\
         export fn first xs -> x : xs~Array Int, len xs > 0, x~Int\n    element xs 0\n\n\
         export fn every xs is -> ys : xs~Array Int, is~List Nat, ys~List Int\n    list.map (element xs) is\n\n\
         lemma inside xs i : xs~Array Int, i~Nat\n    ensures i < len xs\n    proof\n        admit\n\n\
         fn element xs i -> x : xs~Array Int, i~Nat, x~Int\n    have inside xs i\n    walk xs i 0\n\n\
         fn walk xs i k -> x : xs~Array Int, i~Nat, k~Nat, k <= i, i < len xs, x~Int\n    decreasing i - k\n    if k == i then xs[i] else walk xs i (k + 1)\n",
    );
    // Each program calls one of them where the index is past the end, which
    // only an `admit` says can't be, so the index is checked at run time;
    // the first also calls `first` on an array where it holds.
    let program = |elems: &str, call: &str| {
        format!(
            "module p\n\nimport std.system (System, ExitCode)\nimport std.terminal\nimport std.string (debug)\nimport std.array\nimport lib.pick\n\n\
             lemma assumed xs : xs~Array Int\n    ensures len xs > 5\n    proof\n        admit\n\n\
             export fn main args sys -> code : args~List String, sys~System, code~ExitCode\n    let xs = array.from_list {elems}\n    have assumed xs\n    terminal.print_line (debug ({call})) sys.term\n    Success\n"
        )
    };
    for (elems, call, error) in [
        ("[1, 2]", "pick.first xs + pick.at xs 5", "runtime error in `at`: index 5 out of bounds for an array of 2 elements\n"),
        ("[]", "pick.first xs", "runtime error in `first`: index 0 out of bounds for an array of 0 elements\n"),
        ("[1, 2]", "pick.every xs [1, 5]", "runtime error in `every`: index 5 out of bounds for an array of 2 elements\n"),
    ] {
        w.write("prog/p.ck", &program(elems, call));
        for specialized in [true, false] {
            let mut cmd = Command::new(env!("CARGO_BIN_EXE_ckc"));
            cmd.args(["run", "--package", "lib=../lib", "--uses", ".=lib", "p.ck"]).current_dir(w.root.join("prog")).env("CHECKERS_NO_CACHE", "1");
            if !specialized {
                cmd.env("CHECKERS_NO_SPEC", "1");
            }
            let out = cmd.output().expect("run ckc");
            assert_eq!((out.status.code(), text(&out.stderr)), (Some(70), error.to_string()), "{call}, specialized: {specialized}");
        }
    }
}
