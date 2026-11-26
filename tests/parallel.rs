//! Programs checked at the same time in one process (the compiler's unit
//! tests, a language server's checks): each program's `check`s run with
//! its own types and its own `Debug` instances, whatever the others do.

/// A program with `extra` record types of its own before the `check`s, so
/// that each program numbers its types differently.
fn program(extra: usize) -> String {
    let mut src = String::new();
    for i in 0..extra {
        src += &format!("type T{i} = T{i} {{ n: Int }}\n\n");
    }
    src += "check debug \"ab\" == \"\\\"ab\\\"\"\n\n";
    src += "check debug (Some \"ab\") == \"Some \\\"ab\\\"\"\n\n";
    src += "check display \"ab\" [] == \"ab\"\n";
    src
}

#[test]
fn checks_run_with_their_own_program() {
    const THREADS: usize = 8;
    const ROUNDS: usize = 6;
    let workers: Vec<_> = (0..THREADS)
        .map(|t| {
            std::thread::Builder::new()
                .stack_size(1 << 30)
                .spawn(move || {
                    let src = program(t);
                    for _ in 0..ROUNDS {
                        let c = checkers::check("parallel.ck", &src);
                        assert_eq!(c.errors(), 0, "{}", c.report());
                    }
                })
                .unwrap()
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
}
