# Working on Checkers

- **SPEC.md is the source of truth.** Change the spec before the code whenever behavior changes. Record every language decision in the §0 decision log (Dn, date as MM/DD/YYYY, decided/proposed). Ian decides; Claude's recommendations stay marked **(proposed)** until he accepts them.
- **Ian does not read the implementation.** He reviews the spec, examples, and compiler output. Error messages are part of the product: precise span, plain message, a `help:` line when there is an obvious fix.
- **Issue workflow (SPEC §12):** a report is "found X, expected Y" with a `.ck` snippet. First add it as a golden test showing the expected output (`tests/parse/`, `tests/check/`, `tests/types/` for type errors, `tests/stage/` for staged code, `tests/run/` for program behaviour, §13.6), then fix, then `cargo test`.
- `UPDATE_GOLDEN=1 cargo test --test golden` rewrites `.out` files. Read every changed `.out` before committing; never accept output you haven't checked.
- `examples/*.ck` must check with zero diagnostics (enforced by the golden test), except those listed in `examples/PENDING`.
- Keep `cargo clippy` clean. No new dependencies without a reason in the commit message.
- `CHECKERS_DUMP=1 checkers run …` prints each function's elaborated core term as the interpreter compiles it. `CHECKERS_SMT_DUMP=1 checkers check …` prints every SMT query.
- Z3 is linked in (crate `z3-sys`, feature `vendored`, D46): a clean build compiles Z3 from source (needs CMake and a C++ compiler; slow, once). For quicker development builds against an installed libz3: `Z3_LIBRARY_PATH_OVERRIDE=<dir> LD_LIBRARY_PATH=<dir> CARGO_TARGET_DIR=target-dyn cargo test --no-default-features` (the `z3-solver` pip package ships a matching `libz3.so`). Examples that need a later milestone are listed in `examples/PENDING`; their output is pinned in `tests/pending/`.
- Diagnostic codes: `E0001`–`E0099` lexer/layout, `E0100`–`E0199` parser, `E0200`–`E0299` names and types, `E0300`–`E0349` termination, `E0350`–`E0399` declarations (positivity, signatures), `E0400`–`E0449` usage (`own`/`ghost`), `E0450`–`E0499` proofs, `W001`–`W003` naming (§9.7), `W010`–`W019` usage (`W010`: redundant `own`). Never reuse a code for a different meaning (E0107 is retired).
- The standard library lives in `stdlib/*.ck` and is embedded in the binary. A function body consisting of `__builtin` (allowed only in `stdlib/`) is a primitive implemented in Rust.

## Layout

```
src/source.rs        spans, line/column lookup
src/diag.rs          diagnostics and rendering
src/syntax/lexer.rs  characters → tokens → logical lines (INDENT/DEDENT), §9.1
src/syntax/parser.rs recursive descent for §9.2
src/syntax/ast.rs    surface AST
src/syntax/print.rs  S-expression dump used by `checkers parse` and golden tests
src/lint.rs          naming warnings (D21)
src/core.rs          core terms and values, evaluation (NbE), lazy unfolding, unification, printing
src/elab/mod.rs      elaborator state, metas, deferred operator constraints (D38)
src/elab/decls.rs    imports, declarations, positivity, signatures (auto-binding, D10)
src/elab/expr.rs     bidirectional checking of expressions, blocks, `<-`, `try`, `when`/`fork`/`join`
src/elab/pattern.rs  `match` → case trees, exhaustiveness witnesses
src/elab/termination.rs  structural recursion over call-graph SCCs (§5.3)
src/elab/stdlib.rs   embedded standard library loading, program modules from `a/b.ck` (D53)
src/usage.rs         `own`/`ghost` usage (QTT multiplicities)
src/stage.rs         staging (§8.9): expands compile-time functions before erasure; `checkers stage`
src/run/mod.rs       interpreter: evaluator (tail calls), behaviours, `main` (§13)
src/run/ir.rs        erasure: core terms → runtime code
src/run/value.rs     runtime values, structural `==`, `format` (D42)
src/run/num.rs       arbitrary-precision Nat/Int, exact decimals
src/run/builtins.rs  Rust implementations of stdlib `__builtin` functions
src/verify/mod.rs    prover driver: in-process Z3, diagnostics, counterexamples, trust ledger (§7)
src/verify/smt.rs    obligations → SMT-LIB: sorts, datatypes, reflected functions, postconditions
stdlib/*.ck          standard library
tests/golden.rs      golden test runner (tests/parse, tests/check, tests/types, tests/stage, tests/run, examples)
```
