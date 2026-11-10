# Working on Checkers

- **SPEC.md is the source of truth.** Change the spec before the code whenever behavior changes. Record every language decision in the §0 decision log (Dn, date as MM/DD/YYYY, decided/proposed). Ian decides; Claude's recommendations stay marked **(proposed)** until he accepts them.
- **Ian does not read the implementation.** He reviews the spec, examples, and compiler output. Error messages are part of the product: precise span, plain message, a `help:` line when there is an obvious fix.
- **Issue workflow (SPEC §12):** a report is "found X, expected Y" with a `.ck` snippet. First add it as a golden test showing the expected output (`tests/parse/`, `tests/check/`, `tests/types/` for type errors, `tests/stage/` for staged code, `tests/run/` for program behaviour, §13.6; `tests/stress/` for results every multi-threaded schedule must give, §13.5), then fix, then `cargo test`. Tools written in Checkers (`tools/`, D95): formatter cases in `tests/fmt/`, `checkers` commands in `tests/tool/`.
- A test for a **(proposed)** decision goes in `tests/proposed/` (not run) until Ian decides; then it moves to its test directory.
- `UPDATE_GOLDEN=1 cargo test --test golden` rewrites `.out` files. Read every changed `.out` before committing; never accept output you haven't checked.
- `examples/*.ck` must check with zero diagnostics (enforced by the golden test), except those listed in `examples/PENDING`. `tools/checkers.ck` too.
- Two programs (D95, D96): `ckc`, the compiler (Rust, this crate's binary), and `checkers`, the build tool (Checkers, `tools/checkers.ck`, built with `ckc build tools/checkers.ck -o checkers`). The golden tests build `checkers` themselves. `.ck` files in `tools/`, `examples/`, `stdlib/` and `tests/{types,run,stage,stress}` must be formatted (`checkers fmt`); after reformatting, regenerate and read the `.out` files whose spans moved.
- Keep `cargo clippy` clean. No new dependencies without a reason in the commit message.
- All evaluation is native code (D80, SPEC §14): `ckc run`, `check` declarations, and compile-time values in staging. There is no interpreter. Builtins are implemented in `rt/src/builtins.rs`.
- `CHECKERS_NATIVE_DUMP=1 ckc run …` prints native code's first-order form with its reference counting; `CHECKERS_RC_CHECK=1` reports objects still live at exit (only constants' values should be). `CHECKERS_SMT_DUMP=1 ckc check …` prints every SMT query.
- Z3 is linked in (crate `z3-sys`, feature `vendored`, D46): a clean build compiles Z3 from source (needs CMake and a C++ compiler; slow, once). For quicker development builds against an installed libz3: `Z3_LIBRARY_PATH_OVERRIDE=<dir> LD_LIBRARY_PATH=<dir> CARGO_TARGET_DIR=target-dyn cargo test --no-default-features` (the `z3-solver` pip package ships a matching `libz3.so`). Examples that need a later milestone are listed in `examples/PENDING`; their output is pinned in `tests/pending/`.
- Diagnostic codes: `E0001`–`E0099` lexer/layout, `E0100`–`E0199` parser, `E0200`–`E0299` names and types, `E0300`–`E0349` termination, `E0350`–`E0399` declarations (positivity, signatures), `E0400`–`E0449` usage (`own`/`ghost`), `E0450`–`E0499` proofs, `W001`–`W003` naming (§9.7), `W010`–`W019` usage (`W010`: redundant `own`). Never reuse a code for a different meaning (E0107, E0224 and E0453 are retired).
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
src/elab/refine.rs   refinements inside types: inline and function-type refinements, implication, variance, E0262 (D71, D82–D87)
src/elab/termination.rs  structural recursion over call-graph SCCs (§5.3)
src/elab/order.rs   declaration order by dependencies, cycles (D65)
src/elab/stdlib.rs   embedded standard library loading, program modules from `a/b.ck` (D53)
src/usage.rs         `own`/`ghost` usage (QTT multiplicities)
src/stage.rs         staging (§8.9): expands compile-time functions before erasure; `checkers stage`
src/native/ir.rs     erasure: core terms → runtime code (§13.1)
src/native/lower.rs  closure conversion: runtime code → first-order functions (§14)
src/native/rc.rs     reference counting, Perceus style: dup/drop, borrowing, reuse (D74)
src/native/codegen.rs first-order code → Cranelift (JIT and object files)
src/native/eval.rs   compile-time evaluation: `check` and staging, one in-memory module per program (D80)
src/native/mod.rs    `ckc run` (in memory), `ckc build` (link with libcheckers_rt.a)
rt/src/              runtime crate checkers_rt: words and objects, builtins, format, I/O, lock-free scheduler (D77), entry
src/verify/mod.rs    prover driver: in-process Z3, diagnostics, counterexamples, trust ledger (§7)
src/verify/smt.rs    obligations → SMT-LIB: sorts, datatypes, reflected functions, postconditions
stdlib/*.ck          standard library
tools/checkers.ck    `checkers`, the build tool, in Checkers (D95): passes compiler commands to `ckc`; `fmt`
tools/fmt.ck         `checkers fmt`: files, --check, standard input (§15.4)
tools/ck/syntax.ck   the formatter's lexer and layout pass: lines, logical lines, blocks (D93, D99)
tools/ck/format.ck   the formatter: spacing, indentation, alignment, blank lines, comments (D91, D92)
tests/golden.rs      golden test runner (tests/parse, check, types, stage, run, stress, fmt, tool; examples; tools; repository formatting)
```
