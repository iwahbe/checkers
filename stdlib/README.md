# std

The standard library: the package `std`, shipped beside the compiler as source (SPEC §16). A module here is imported as `std.NAME` (`import std.list`); the prelude's types (`Int`, `Nat`, `String`, `List`, `Option`, `Result`, …) are in scope in every module.

Functions with effects take a capability: `Term` for the terminal, `Fs` for files, `Proc` for other programs, `Sched` for concurrency. A program's `main` receives them all in `System`. The standard library's proofs are checked with every program that uses it; its builtins are implemented in the runtime, and its axioms are listed by `checkers trust`.
