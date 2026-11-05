# Working on Checkers

- **SPEC.md is the source of truth.** Change the spec before the code whenever behavior changes. Record every language decision in the §0 decision log (Dn, date as MM/DD/YYYY, decided/proposed). Ian decides; Claude's recommendations stay marked **(proposed)** until he accepts them.
- **Ian does not read the implementation.** He reviews the spec, examples, and compiler output. Error messages are part of the product: precise span, plain message, a `help:` line when there is an obvious fix.
- **Issue workflow (SPEC §12):** a report is "found X, expected Y" with a `.ck` snippet. First add it as a golden test under `tests/parse/` or `tests/check/` showing the expected output, then fix, then `cargo test`.
- `UPDATE_GOLDEN=1 cargo test --test golden` rewrites `.out` files. Read every changed `.out` before committing; never accept output you haven't checked.
- `examples/*.ck` must check with zero diagnostics (enforced by the golden test).
- Keep `cargo clippy` clean. No new dependencies without a reason in the commit message.
- Diagnostic codes: `E0001`–`E0099` lexer/layout, `E0100`–`E0199` parser, `W001`–`W003` naming (§9.7). Never reuse a code for a different meaning.

## Layout

```
src/source.rs        spans, line/column lookup
src/diag.rs          diagnostics and rendering
src/syntax/lexer.rs  characters → tokens → logical lines (INDENT/DEDENT), §9.1
src/syntax/parser.rs recursive descent for §9.2
src/syntax/ast.rs    surface AST
src/syntax/print.rs  S-expression dump used by `checkers parse` and golden tests
src/lint.rs          naming warnings (D21)
tests/golden.rs      golden test runner
```
