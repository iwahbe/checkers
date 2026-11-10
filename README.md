# Checkers

A functional, immutable language with dependent types, a built-in theorem prover, sealed module interfaces, and race-free concurrency (cowns and `when`). Source files end in `.ck`.

```
fn skip_ws src i -> j : src~Bytes, i~Nat, i <= len src,
                        j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and is_ws src[i]
        skip_ws src (i + 1)
    else
        i
```

Types are written only as constraints (`i~Nat, i <= len src`); the compiler proves the rest. [`sort.ck`](examples/sort.ck) is an insertion sort whose result is proven sorted and a permutation of its input; [`resort.ck`](examples/resort.ck) imports it and, seeing only its interface, proves that sorting twice is sorting once. Examples: [`json.ck`](examples/json.ck), which reads JSON with the standard library's [`std.json`](stdlib/json.ck), a parser whose bounds checks, termination, and round-trip property are proven; [`wc.ck`](examples/wc.ck), a CLI tool using linear capabilities; [`log.ck`](examples/log.ck), concurrency with cowns and `when`; [`format.ck`](examples/format.ck), a typed `fmt` whose format string is parsed at compile time.

**[SPEC.md](SPEC.md) is the definition of the language.** The implementation follows it.

## Status

| Milestone | State |
|---|---|
| M0 Front end: lexer with layout, parser, naming warnings, diagnostics | done |
| M1 Type checker: dependent types, exhaustive `match`, termination, `own`/`ghost` usage | done (refinements recorded, proven in M3) |
| M2 Interpreter: `checkers run`, `check` evaluation, files and terminal, linear resources | done |
| M3 Prover: pre/postconditions, refinements, invariants, lemmas, Z3, trust ledger | done: `examples/sort.ck` (insertion sort) and `wc.ck` verify |
| M4 Modules: files, sealing, exported lemmas, multi-module proofs | done: [`resort.ck`](examples/resort.ck) uses `sort` through its exported lemma only |
| M5 Well-founded recursion, lexicographic `decreasing` | done: merge sort in [`parallel.ck`](examples/parallel.ck); [`json.ck`](stdlib/json.ck) (now `std.json`) verifies, trusting its two `admit`s and two axioms about decimal numbers |
| M6 Staging: `comptime` parameters, compile-time expansion, `checkers stage` | done: [`format.ck`](examples/format.ck), a typed `fmt` whose format string is parsed at compile time |
| M7 Multi-threaded behaviours (Verona scheduling), `par` on threads, cown invariants, actors | done: [`log.ck`](examples/log.ck) proves its cown invariant and runs; `checkers run --threads N`; stress tests in `tests/stress/` |
| M8 Native code: Cranelift, closure conversion, reference counting with reuse, tail calls, `checkers build`, lock-free scheduler | done: [`wc.ck`](examples/wc.ck) 45× faster than the interpreter, which is now removed (SPEC D80): `check` and staging run native code too |
| M10 Refined function types | done |
| M11 `checkers`, the build tool in Checkers, and `checkers fmt` | done: [`tools/`](tools) |
| M12 Faster checking: Z3 answer cache, work limits | done |
| M13 The standard library as the package `std`, read from [`stdlib/`](stdlib) at each check: `import std.list` | done |
| M14 Packages: `checkers.json`, `checkers.lock`, git and path dependencies, minimal version selection | done |
| M15 | see SPEC §10 (M9, a shell, was removed: D81) |

## Usage

Z3 is built from source and linked into the binary (D46), so the first build takes several minutes and needs CMake and a C++ compiler. Nothing else needs installing.

```
cargo build --release
target/release/ckc run examples/wc.ck FILE         # type-check, then run `main`
target/release/ckc check examples/sort.ck           # type-check, run the `check`s, prove
target/release/ckc trust examples/sort.ck           # what the proof relies on: Z3, admits, checks, builtins
target/release/ckc parse examples/json.ck           # print the syntax tree
target/release/ckc build tools/checkers.ck -o target/release/checkers
target/release/checkers fmt examples                # format; `checkers check …` etc. run `ckc`
cd my_package && checkers run                        # with checkers.json: fetch dependencies, then run main.ck
```

`ckc` is the compiler; `checkers` is the build tool, written in Checkers (SPEC §15, D95).

## Tests

```
cargo test                                    # unit + golden tests
UPDATE_GOLDEN=1 cargo test --test golden      # accept new golden output (review the diff!)
```

Golden tests live in `tests/parse/` (syntax tree), `tests/check/` (parse diagnostics) and `tests/types/` (type-checker contract: accepted and rejected programs): each `NAME.ck` has a `NAME.out`. `tests/run/NAME.args` runs a program (first line) with arguments (other lines) and stdin `NAME.in`; `NAME.out` holds its stdout, stderr and exit code (SPEC §13.6). Every file in `examples/` must check with no diagnostics.

## Reporting a problem

Open an issue in the form **"found X, expected Y"** with a `.ck` snippet. It becomes a golden test before it is fixed (SPEC §12).
