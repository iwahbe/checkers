# Checkers

Checkers is a functional language whose compiler proves your programs correct: every array index, every subtraction, every loop's end and every postcondition you write, before the program runs.

```checkers
module bounds

# The position of the first non-space byte at or after `i`. The prover
# checks every index, that the recursion ends, and the postcondition.
fn skip_spaces src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and src[i] == ' ' then skip_spaces src (i + 1) else i

check skip_spaces b"  x" 0 == 2
```

A function's signature is a list of constraints: its types (`src~Bytes`) and what must hold of its arguments and its result (`i <= len src`, `j <= len src`). The compiler turns each index, each call and each `decreasing` measure into a proof obligation and hands it to the Z3 theorem prover; a program with an obligation it can't prove doesn't compile, and the error shows a counterexample.

## What it has

- **Proofs without proof scripts.** Pre- and postconditions, refinement types (`type Even = n~Nat, n % 2 == 0`), lemmas and induction, discharged by Z3. When Z3 needs help, a `have` line names the fact to use.
- **Dependent types**, written as constraints: types can mention values (`Parsed Json src i`), and a function's result type can depend on its arguments.
- **Effects through capabilities.** A function that reads files takes an `Fs`; one without it can't touch the file system. Open files and child processes are linear: forgetting to close one is a compile error.
- **Concurrency without data races or deadlocks.** Values shared between threads live in cowns; behaviours (`when`) that name a cown run one at a time, in order. `fork`, `join` and `par` add parallelism.
- **Native code.** Programs compile to machine code with Cranelift, with reference counting and in-place reuse; `check` declarations and compile-time code run natively too.
- **Tools.** `checkers fmt`, a language server (hover, go to definition, references, highlighting, diagnostics as you type), packages from git, and this site's documentation generator.

## Start

- [Tour](tour.md): the language in ten examples.
- [Install](install.md): build from source, set up an editor.
- [Documentation](docs.md): the standard library, by version.
- [SPEC.md](https://github.com/iwahbe/checkers/blob/main/SPEC.md): the definition of the language and the log of its design decisions.

Checkers runs on Linux (x86-64) and macOS (Apple silicon). It is young: v0.0.1 is its first release.
