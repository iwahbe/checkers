# The Checkers Reference

This is the reference for the Checkers language as it is today: every rule a program must follow, what each construct means, and what the compiler proves. It is meant to be read in order by someone learning the whole language, and searched by someone who needs one rule. The [Tour](../tour.md) is the shorter introduction; the [Packages](../packages.md) pages document the standard library's modules one declaration at a time.

Every example on these pages is compiled when the site is built. An example marked as failing (its header says `compile_fail` and an error code) is checked to fail with that error, so each rule shown that way is the compiler's real behaviour. Examples without a `module` line are each a module of their own.

## Chapters

1. [Notation](notation.md): how the rules on these pages are written.
2. [Lexical structure](lexical.md): characters, tokens, literals, comments, and how lines and indentation make blocks.
3. [Modules and packages](modules.md): files, imports, exports, sealing, and packages with dependencies.
4. [Declarations](declarations.md): functions, enums, records, type aliases, constants, `check`, and the order they are checked in.
5. [Types and constraints](types.md): constraint lists, the built-in types, refinements, function types, generics, `ghost`, `own` and `comptime`.
6. [Expressions](expressions.md): blocks, `let`, application, operators, `if`, lambdas, `try`, and what each evaluates to.
7. [Patterns and `match`](patterns.md): patterns, guards, which cases a `match` must cover, and arms that never run.
8. [Recursion and termination](termination.md): structural recursion, `decreasing`, guessed measures, and `partial`.
9. [Proofs](proofs.md): obligations, the facts the prover knows, lemmas, `have`, `forall`, and what a proof rests on.
10. [Classes](classes.md): classes, instances, operators through classes, and classes over type constructors.
11. [Capabilities and resources](effects.md): `main`, authority capabilities, resources used exactly once, files and processes.
12. [Concurrency](concurrency.md): cowns, behaviours, futures and `par`.
13. [Staging](staging.md): `comptime` parameters and code that runs while compiling.
14. [Documentation comments](documentation.md): descriptions, links to symbols, and code that is compiled.
15. [Running programs](execution.md): erasure, evaluation order, `format`, run-time checks and exit codes.
16. [Diagnostics](diagnostics.md): every error and warning the compiler reports.

The standard library is outside this reference except where the language depends on it: the prelude's types and classes ([Types](types.md), [Classes](classes.md)) and the capability types ([Capabilities](effects.md)).
