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

Types are written only as constraints (`i~Nat, i <= len src`); the compiler proves the rest. [`sort.ck`](examples/sort.ck) is an insertion sort whose result is proven sorted and a permutation of its input. Examples: [`json.ck`](examples/json.ck), a JSON parser whose bounds checks, termination, and round-trip property are proven; [`wc.ck`](examples/wc.ck), a CLI tool using linear capabilities; [`log.ck`](examples/log.ck), concurrency with cowns and `when`.

**[SPEC.md](SPEC.md) is the definition of the language.** The implementation follows it.

## Status

| Milestone | State |
|---|---|
| M0 Front end: lexer with layout, parser, naming warnings, diagnostics | done |
| M1 Type checker: dependent types, exhaustive `match`, termination, `own`/`ghost` usage | done (refinements recorded, proven in M3) |
| M2 Interpreter: `checkers run`, `check` evaluation, files and terminal, linear resources | done |
| M3 Prover: pre/postconditions, refinements, invariants, lemmas, Z3, trust ledger | done: `examples/sort.ck` (insertion sort) and `wc.ck` verify |
| M4 Modules, sealing, exported lemmas | next |
| M4–M9 | see SPEC §10 |

## Usage

Z3 is built from source and linked into the binary (D46), so the first build takes several minutes and needs CMake and a C++ compiler. Nothing else needs installing.

```
cargo build --release
target/release/checkers run examples/wc.ck FILE    # type-check, then run `main`
target/release/checkers check examples/sort.ck      # type-check, run the `check`s, prove
target/release/checkers trust examples/sort.ck      # what the proof relies on: Z3, admits, checks
target/release/checkers parse examples/json.ck      # print the syntax tree
```

## Tests

```
cargo test                                    # unit + golden tests
UPDATE_GOLDEN=1 cargo test --test golden      # accept new golden output (review the diff!)
```

Golden tests live in `tests/parse/` (syntax tree), `tests/check/` (parse diagnostics) and `tests/types/` (type-checker contract: accepted and rejected programs): each `NAME.ck` has a `NAME.out`. `tests/run/NAME.args` runs a program (first line) with arguments (other lines) and stdin `NAME.in`; `NAME.out` holds its stdout, stderr and exit code (SPEC §13.6). Every file in `examples/` must check with no diagnostics.

## Reporting a problem

Open an issue in the form **"found X, expected Y"** with a `.ck` snippet. It becomes a golden test before it is fixed (SPEC §12).
