//! Checking takes time in proportion to the program: a chain of n operators
//! (`1 + 1 + … + 1`) is a tree n deep, and work done again at each level for
//! everything below it makes the time grow with n². And a literal in the
//! program doesn't make checking slower than the work its types need.

use std::path::Path;
use std::process::Command;

/// The types and checks phases' time, in milliseconds, for `check <expr> == n`.
fn check_time(dir: &Path, name: &str, term: &str, op: &str, n: usize, wrap: fn(String) -> String) -> f64 {
    let chain = vec![term; n].join(&format!(" {op} "));
    source_time(dir, name, &format!("module {name}\n\ncheck {} == {n}\n", wrap(chain)))
}

/// The types and checks phases' time, in milliseconds, for module `name`.
fn source_time(dir: &Path, name: &str, source: &str) -> f64 {
    let file = dir.join(format!("{name}.ck"));
    std::fs::write(&file, source).unwrap();
    // The fastest of a few runs: the least disturbed by other tests.
    (0..3)
        .map(|_| {
            let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
                .args(["check", "--no-cache", &format!("{name}.ck")])
                .current_dir(dir)
                .env("CHECKERS_PHASE_TIME", "1")
                .output()
                .expect("run ckc");
            let err = String::from_utf8_lossy(&out.stderr);
            assert!(out.status.success(), "{name}: {err}{}", String::from_utf8_lossy(&out.stdout));
            let prefix = format!("{name}.ck: ");
            let times: Vec<f64> = err
                .lines()
                .filter_map(|l| l.strip_prefix(&prefix))
                .filter(|l| l.starts_with("types ") || l.starts_with("checks "))
                .map(|l| l.split(' ').nth(1).unwrap().parse::<f64>().unwrap())
                .collect();
            assert_eq!(times.len(), 2, "{name}: no phase times in\n{err}");
            times.iter().sum::<f64>()
        })
        .fold(f64::INFINITY, f64::min)
}

/// Four times the operators may take at most ten times as long: quadratic
/// work takes sixteen times. (Linear work takes four to six: code
/// generation's share grows a little faster than the program.)
fn assert_linear(name: &str, term: &str, op: &str, wrap: fn(String) -> String) {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let small = check_time(&dir, &format!("{name}1000"), term, op, 1000, wrap);
    let large = check_time(&dir, &format!("{name}4000"), term, op, 4000, wrap);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(large < 10.0 * small.max(20.0), "{name}: 1000 operators took {small:.0} ms, 4000 took {large:.0} ms");
}

#[test]
fn a_chain_of_additions_checks_in_linear_time() {
    assert_linear("add", "1", "+", |c| c);
}

#[test]
fn a_chain_of_concatenations_checks_in_linear_time() {
    assert_linear("concat", "\"a\"", "++", |c| format!("len ({c})"));
}

/// A recursive function building a list of `n` in an accumulator: running
/// it takes n steps, each with the list so far.
const BUILD: &str = "fn build n acc -> r : n~Nat, acc~List Nat, r~List Nat
    decreasing n
    if n == 0 then acc else build (n - 1) (0 :: acc)

";

/// Checking `source(name, n)` for a `large` literal may take at most `factor`
/// times as long as for a `small` one (time below 20 ms doesn't count).
fn assert_literal_costs(name: &str, small: usize, large: usize, factor: f64, source: fn(&str, usize) -> String) {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let time = |n: usize| source_time(&dir, &format!("{name}{n}"), &source(&format!("{name}{n}"), n));
    let (t_small, t_large) = (time(small), time(large));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        t_large < factor * t_small.max(20.0),
        "{name}: {small} took {t_small:.0} ms, {large} took {t_large:.0} ms"
    );
}

/// A type that needs a call's value: checking runs the call, each step
/// taking the same time however long the list built so far. Four times the
/// steps may take at most eight times as long: quadratic work takes sixteen.
#[test]
fn running_a_call_while_checking_takes_linear_time() {
    assert_literal_costs("by_type", 2000, 8000, 8.0, |name, n| {
        format!(
            "module {name}\n\n{BUILD}fn pick xs -> t : xs~List Nat, t~Type\n    match xs\n        []     -> Bool\n        _ :: _ -> Nat\n\n\
             export fn by_type -> v : v~pick (build {n} [])\n    0\n"
        )
    });
}

/// A field of a call's result, where no type needs the call's value:
/// checking doesn't run it, so the literal doesn't change the time. (Running
/// it would stop at the unfolding limit, still many times as long.)
#[test]
fn reading_a_field_of_a_call_does_not_run_it() {
    assert_literal_costs("by_field", 2000, 2_000_000, 3.0, |name, n| {
        format!(
            "module {name}\n\nrecord Box\n    value~Nat\n\n{BUILD}fn wrap xs -> r : xs~List Nat, r~Box\n    match xs\n        []     -> Box 0\n        _ :: _ -> Box 1\n\n\
             export fn by_field -> v : v~Nat\n    (wrap (build {n} [])).value\n"
        )
    });
}

/// The peak heap, in bytes, of `ckc check` on a function adding its
/// argument to itself n times, `x + x + … + x`, and a `check` calling it. `x`
/// is an `Int` of any size, so each `+` tests for small integers: about a
/// block per operator.
#[cfg(target_os = "linux")]
fn check_peak_heap(dir: &Path, name: &str, n: usize) -> u64 {
    let chain = vec!["x"; n].join(" + ");
    source_usage(dir, name, &format!("module {name}\n\nfn f x -> r : x~Int, r~Int\n    {chain}\n\ncheck f 1 == {n}\n")).1
}

/// The CPU time, in milliseconds, and the peak heap, in bytes, of `ckc
/// check` on module `name`.
///
/// CPU time, unlike the phases' times, doesn't count waiting for a CPU, so
/// it varies less when other tests are running. It is the child's, which
/// the kernel reports when it is reaped; `wait4` reaps this child alone, so
/// other tests' children, running at the same time, don't count.
///
/// The peak heap is the most memory `ckc` held allocated at once
/// (`CHECKERS_PEAK_HEAP=1`): exact, and the same in every run. The peak
/// resident memory isn't: it holds about 90 MB that don't grow with the
/// program (the compiler's code, Z3's memory), and the allocator takes
/// memory from the system in steps of 5 MB to 80 MB, so what a doubling
/// of 2,000 `let`s added to it ranged from half to twice what the program
/// held (2,000 to 4,000 lets of closures added 8 MB to 11 MB, 4,000 to
/// 8,000 added 32 MB to 33 MB; the heap's peak grew by 16 MB and 33 MB).
#[cfg(target_os = "linux")]
fn source_usage(dir: &Path, name: &str, source: &str) -> (f64, u64) {
    let file = dir.join(format!("{name}.ck"));
    std::fs::write(&file, source).unwrap();
    let err_path = dir.join(format!("{name}.err"));
    let child = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["check", "--no-cache", &format!("{name}.ck")])
        .current_dir(dir)
        .env("CHECKERS_PEAK_HEAP", "1")
        .stdout(std::process::Stdio::null())
        .stderr(std::fs::File::create(&err_path).unwrap())
        .spawn()
        .expect("run ckc");
    let pid = child.id() as libc::pid_t;
    let mut status = 0;
    // SAFETY: `rusage` is plain data; `wait4` writes `status` and `usage`.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    let reaped = loop {
        let r = unsafe { libc::wait4(pid, &mut status, 0, &mut usage) };
        if r != -1 || std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
            break r;
        }
    };
    assert_eq!(reaped, pid, "{name}: wait4: {}", std::io::Error::last_os_error());
    // `child` is reaped already: dropping it neither waits nor kills.
    drop(child);
    let err = std::fs::read_to_string(&err_path).unwrap();
    assert!(libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0, "{name}: ckc failed:\n{err}");
    let heap = err
        .lines()
        .find_map(|l| l.strip_prefix("peak heap: ")?.strip_suffix(" bytes")?.parse().ok())
        .unwrap_or_else(|| panic!("{name}: no peak heap in\n{err}"));
    let ms = |t: libc::timeval| t.tv_sec as f64 * 1000.0 + t.tv_usec as f64 / 1000.0;
    (ms(usage.ru_utime) + ms(usage.ru_stime), heap)
}

/// Code generation keeps memory in proportion to the function: Cranelift's
/// SSA builder, given a variable per `let`, keeps a map per variable as long
/// as the function's block count, n² for n additions. 4,000, 8,000 and
/// 16,000 operators peak at a heap of 179 MB, 356 MB and 711 MB. (Their
/// peak resident memory was 242–256 MB, 412–416 MB and 732–737 MB, and with
/// a variable per `let` 372–376 MB, 1,160–1,164 MB and 4,243–4,247 MB.) A
/// fixed part cancels out of the increments: linear memory adds twice as
/// much for the second 8,000 operators as for the 4,000 before them, n² four
/// times. The second may add at most three times the first (2.00; 3.96 with
/// a block-count map per variable).
#[cfg(target_os = "linux")]
#[test]
fn additions_compile_in_linear_memory() {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-memory", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let [small, medium, large] = [4000, 8000, 16000].map(|n| check_peak_heap(&dir, &format!("mem{n}"), n));
    let _ = std::fs::remove_dir_all(&dir);
    let (first, second) = (medium.saturating_sub(small), large.saturating_sub(medium));
    let mb = |b: u64| b / (1 << 20);
    assert!(
        second < 3 * first,
        "4000 operators took a heap of {} MB at peak, 8000 took {} MB, 16000 took {} MB: the second 8000 added {:.2} times what the 4000 before them did",
        mb(small),
        mb(medium),
        mb(large),
        second as f64 / first as f64
    );
}

/// The least CPU time of a few runs of `ckc check`, and its peak heap, on a
/// function of 4,000, 8,000 and 16,000 `let`s, `let a{i} = {step(a{i-1})}`,
/// over values of type `ty`, with no `check`: only elaboration is measured.
/// The least of a few runs is the least disturbed by other tests.
#[cfg(target_os = "linux")]
fn lets_usage(tag: &str, ty: &str, step: fn(&str) -> String) -> [(f64, u64); 3] {
    lets_usage_by(tag, ty, &|i| format!("    let a{i} = {}
", step(&format!("a{}", i - 1))))
}

/// `lets_usage`, with `line(i)` the lines defining `a{i}` from `a{i-1}`.
#[cfg(target_os = "linux")]
fn lets_usage_by(tag: &str, ty: &str, line: &dyn Fn(usize) -> String) -> [(f64, u64); 3] {
    lets_usage_in(tag, "", &format!("x -> r : x~{ty}, r~{ty}"), line)
}

/// `lets_usage_by`, with `f`'s parameters and signature `sig` (`x` among
/// them), after the lines `imports`.
#[cfg(target_os = "linux")]
fn lets_usage_in(tag: &str, imports: &str, sig: &str, line: &dyn Fn(usize) -> String) -> [(f64, u64); 3] {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-{tag}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let usage = LETS.map(|n| {
        let name = format!("{tag}{n}");
        let mut s = format!("module {name}\n\n{imports}export fn f {sig}\n    let a0 = x\n");
        for i in 1..=n {
            s += &line(i);
        }
        s += &format!("    a{n}\n");
        (0..7).map(|_| source_usage(&dir, &name, &s)).fold((f64::INFINITY, u64::MAX), |(t, m), (t2, m2)| (t.min(t2), m.min(m2)))
    });
    let _ = std::fs::remove_dir_all(&dir);
    usage
}

/// The sizes `lets_usage` measures. The peak heap is the larger of the
/// standard library's checking and the function's: below about 4,000 `let`s,
/// the standard library's can be the larger, and what a doubling adds to the
/// peak isn't what the function's memory grew by.
#[cfg(target_os = "linux")]
const LETS: [usize; 3] = [4000, 8000, 16000];

/// Linear memory and time for `lets_usage`'s measurements.
///
/// Memory: what each doubling adds to the peak heap, twice as much the
/// second time for linear memory, four times for quadratic; the fixed part
/// (the standard library) cancels out. The second may add up to three times
/// the first.
///
/// Time per instruction grows with the memory a run touches, so what a
/// doubling adds to the time doesn't tell quadratic work from cache misses:
/// four times the lets may take at most four times as long, as linear work
/// with any fixed part does.
#[cfg(target_os = "linux")]
fn assert_lets_linear(tag: &str, [a, b, c]: [(f64, u64); 3]) {
    let mb = |bytes: u64| bytes as f64 / (1 << 20) as f64;
    let (first, second) = (mb(b.1) - mb(a.1), mb(c.1) - mb(b.1));
    let [n0, n1, n2] = LETS;
    assert!(
        second <= 3.0 * first,
        "{tag}: peak heap: {n0} to {n1} lets added {first:.1} MB, {n1} to {n2} added {second:.1} MB"
    );
    assert!(c.0 <= 4.0 * a.0, "{tag}: CPU time: {n0} lets took {:.0} ms, {n2} took {:.0} ms", a.0, c.0);
}

/// A function of n `let`s, each joining a string to the one before. `a{i}`'s
/// value, `x ++ "a" ++ … ++ "a"`, is i deep, and each `let` after it refers
/// to it. Shared, the values take memory in proportion to n; copied for each
/// local that holds one, they took n²/2 (2,000 took 350 MB and 2.8 s to
/// elaborate, 8,000 took 4.6 GB and 44 s). So did the names of every local in
/// scope, kept for each operator's message. (Now 4,000 to 8,000 lets add
/// 10 MB to the peak heap, 8,000 to 16,000 21 MB, and 16,000 take 1.4 times
/// the time of 4,000. Without sharing, 2,000 to 4,000 lets added 850 MB to
/// the peak resident memory, 4,000 to 8,000 3,396 MB, and 8,000 took 15
/// times the time of 2,000.)
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_lets_checks_in_linear_time_and_memory() {
    assert_lets_linear("by_let", lets_usage("by_let", "String", |a| format!("{a} ++ \"a\"")));
}

/// A function of n `let`s, each binding a closure over the one before, and
/// the next calling it. Each of these walked or copied every local before
/// it: a closure's environment, copied for each call of it and each local
/// after it; each call's question whether the closure captured an effect,
/// asked by writing out the values of the locals it refers to; the name
/// chosen for its type's parameter in the index's hover text, compared with
/// every local's; native code's compiler, rewriting all the code after each
/// closure's `let` (and keeping each copy until the end), then looking
/// through it for a use of the closure; and the inliner, putting each
/// erased `let` into all the code after it. 2,000 lets took 4.5 s and
/// 2.4 GB, 8,000 ran out of memory. (Now 4,000 to 8,000 lets add 32 MB to
/// the peak heap, 8,000 to 16,000 64 MB, and 16,000 take 2.1 times the time
/// of 4,000.)
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_lets_of_closures_checks_in_linear_time_and_memory() {
    assert_lets_linear("by_closure", lets_usage_by("by_closure", "Int", &|i| format!("    let g{i} = \\y -> y + a{}\n    let a{i} = g{i} 1\n", i - 1)));
}

/// `a_chain_of_lets_of_closures_checks_in_linear_time_and_memory`, in a
/// function given a capability. Each call of a closure asks whether it
/// captured one, and with one in scope, the answer was looked for in the
/// closure's value written out: `g{i}`'s refers to `a{i-1}`, whose value,
/// `x + 1 + … + 1`, is i deep. 8,000 lets took 9.3 times as long as 2,000
/// (7.35 s and 0.79 s, release). Which bound locals a local refers to is
/// decided once, from the term that defined it: 1.6 times as long (0.75 s
/// and 0.46 s), as without the capability. (16,000 take 2.2 times the time
/// of 4,000.)
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_lets_of_closures_given_an_effect_checks_in_linear_time_and_memory() {
    assert_lets_linear(
        "by_closure_fx",
        lets_usage_in("by_closure_fx", "import std.terminal (Term)\n\n", "x term -> r : x~Int, term~Term, r~Int", &|i| {
            format!("    let g{i} = \\y -> y + a{}\n    let a{i} = g{i} 1\n", i - 1)
        }),
    );
}

/// A function of n `let`s, each adding one to the one before. Each `+` asks
/// what its operands are known to be at compile time, which bounds its
/// range. Asked of a local by evaluating and quoting its value, `x + 1 + … +
/// 1`, each `+` walked every one before it: 8,000 lets took 16 times as
/// long as 2,000 (91 s and 5.6 s). What a local is known to be is decided
/// once, from the term that defined it: 1.4 to 1.8 times as long. (16,000
/// take 1.5 times the time of 4,000.)
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_additions_in_lets_checks_in_linear_time_and_memory() {
    assert_lets_linear("by_add", lets_usage("by_add", "Int", |a| format!("{a} + 1")));
}

/// A function of n `let`s, each calling a class's function on the one
/// before. Each call keeps its context for later: to find its instance's
/// dictionary, and to check the call once it is found. Copied, each kept
/// context held every local in scope, n²/2 for n calls: 2,000 took 1.3 GB
/// and 4,000 took 5.1 GB. Persistent, they take 141 MB and 157 MB, and
/// 8,000 191 MB. Each call also walked every local, to find the
/// dictionaries in scope and the locals an unknown depends on, and built
/// an environment of them all to evaluate its dictionary: 8,000 took 7.3
/// times as long as 2,000 with these, 2.8 times without. And each call
/// looked its function's name up among the locals, a walk over all of them
/// when the name isn't a local's: 16,000 took 6.7 times as long as 4,000
/// (4.8 s and 0.72 s, release), and 32,000 took 34 s. Looked up in a map of
/// the locals' names, 16,000 take 2.2 times as long as 4,000 (1.05 s and
/// 0.47 s), and 32,000 1.7 s; 4,000 to 8,000 lets add 54 MB to the peak
/// heap, 8,000 to 16,000 108 MB.
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_class_calls_in_lets_checks_in_linear_time_and_memory() {
    assert_lets_linear("by_class", lets_usage("by_class", "Int", |a| format!("add {a} 1")));
}
