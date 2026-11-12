# Tour

Short examples, each a whole module (one shows an error on purpose). Check one with `checkers check FILE.ck`, run one with `checkers run FILE.ck`.

## Functions and constraints

```checkers
module first

# The largest of two numbers. The conditions after `:` are the signature:
# types are written as constraints (`a~Int`), next to what must hold.
fn max a b -> m : a~Int, b~Int, m~Int, m >= a, m >= b, m == a or m == b
    if a >= b then a else b

check max 3 7 == 7
```

`a~Int` says `a` is an integer. The constraints on `m`, the result, are the postcondition: the compiler proves them for every input, not just the ones a test tries. `check` runs an expression at compile time and fails the build if it is false.

## Indexes, termination and counterexamples

```checkers
module bounds

fn skip_spaces src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and src[i] == ' ' then skip_spaces src (i + 1) else i
```

`src[i]` is allowed only where `i < len src` can be proven: here the `if` says so. The recursion isn't on a smaller piece of `src`, so `decreasing` gives a measure that must shrink at each call; the compiler proves that too. When a proof fails, the error says what couldn't be proven and shows a counterexample:

```checkers
module wrong

fn last xs -> x : xs~Bytes, x~U8
    xs[len xs - 1]
```

```
error[E0450]: cannot prove that this `Nat` subtraction stays at or above zero
 --> wrong.ck:4:8
  |
4 |     xs[len xs - 1]
  |        ^^^^^^^^^^ `-` on `Nat` needs the left side to be at least the right
  = note: counterexample: xs = b""
  = help: check it first (`if a >= b then a - b else …`), or use `Int`

wrong.ck: 1 error, 0 warnings
```

## Refinement types

```checkers
module evens

type Even = n~Nat, n % 2 == 0

fn double n -> e : n~Nat, e~Even
    n + n

# A `Nat` is an `Int` for free; an `Int` where a `Nat` is expected is
# something to prove.
fn halve e -> n : e~Even, n~Nat, n + n == e
    e / 2
```

A type can carry a condition. `Nat` itself is `n~Int, n >= 0`, and the fixed-width types (`U8`, `U32`, …) are refinements of it.

## Induction

```checkers
module sort

import std.list (sorted, perm)

# The first element, or `d` for an empty list.
fn first_or d xs -> r : d~Int, xs~List Int, r~Int
    match xs
        []     -> d
        x :: _ -> x

fn insert x ys -> zs : x~Int, ys~List Int, sorted ys,
                       zs~List Int, sorted zs, perm (x :: ys) zs,
                       first_or x zs == x or first_or x zs == first_or x ys
    match ys
        []        -> [x]
        y :: rest -> if x <= y then x :: ys else y :: insert x rest

export fn sort xs -> ys : xs~List Int, ys~List Int, sorted ys, perm xs ys
    match xs
        []        -> []
        x :: rest -> insert x (sort rest)

# Sorting a sorted list changes nothing. A recursive call to the lemma is
# the induction hypothesis.
export lemma sort_of_sorted xs : xs~List Int, sorted xs
    ensures sort xs == xs
    proof
        match xs
            []        -> auto
            x :: rest -> have sort_of_sorted rest
```

An insertion sort whose result is proven sorted and a permutation of its input. Each recursive call may assume its own postcondition (it terminates, so this is induction), and Z3 does the rest. An importer sees only `sort`'s signature and the lemmas the module exports, and builds on them:

```checkers
module sorting

import std.list (sorted)
import sort (sort)

export lemma sort_twice xs : xs~List Int
    ensures sort (sort xs) == sort xs
    proof
        have sort.sort_of_sorted (sort xs)
```

## What a proof rests on

`checkers trust FILE.ck` lists every fact a module relies on and how it was established: proven by Z3 (with the query's hash), computed at compile time, an axiom of the standard library, or an `admit` (an unproven assumption, allowed while developing; `checkers build --release` refuses a program that has one).

```
$ checkers trust bounds.ck
bounds.ck:3:68  smt      postcondition of `skip_spaces`: i <= j (for `skip_spaces src (i + 1)`, line 5)  [051dfac6c486bedd]
bounds.ck:3:68  smt      postcondition of `skip_spaces`: i <= j (for `i`, line 5)  [9a02b784e88ec4ab]
bounds.ck:3:76  smt      postcondition of `skip_spaces`: j <= len src (for `skip_spaces src (i + 1)`, line 5)  [4601f37fe1e2cee6]
bounds.ck:3:76  smt      postcondition of `skip_spaces`: j <= len src (for `i`, line 5)  [6776c8289821b1aa]
bounds.ck:4:16  smt      `Nat` subtraction `len src - i` stays at or above zero  [57f366ca1bca7d7c]
bounds.ck:5:24  smt      index in bounds: i < len src  [fa48a08a056d7078]
bounds.ck:5:43  smt      precondition of `skip_spaces`: i <= len src  [8ad758cf927bb736]
bounds.ck:5:43  smt      termination of `skip_spaces`: `decreasing len src - i` gets smaller  [2c6aafd276720832]
solver: Z3 5.3.3.0
```

## Effects are capabilities

```checkers
module hello

import std.system (System, ExitCode)
import std.terminal

# `main` gets the program's arguments and its authority, `System`. Printing
# needs `Term`, part of it: a function without it can't print.
export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "hello" sys.term
    Success
```

Every function is a mathematical function: the same arguments give the same result. Effects go through capabilities passed as arguments: `Term` for the terminal, `Fs` for files, `Proc` for other programs, `Env` for the environment. An open `File` or a child process is a resource: it must be used exactly once, so a file that is never closed is a compile error.

## Concurrency: cowns and behaviours

```checkers
module counter

import std.system (System, ExitCode)
import std.cown (Cown)
import std.future (Future)
import std.terminal

# A cown owns a value. Behaviours (`when`) that name it run one at a time,
# in the order they were scheduled, and hand back its new value.
export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let hits = cown.new 0 sched
    when n = hits using sched
        n + 1
    when n = hits using sched
        terminal.print_line ("hits: " ++ format n) term
        n
    a <- fork using sched
        20
    b <- fork using sched
        22
    done <- join x = a, y = b using sched
        if x + y == 42 then Success else Failure 1
    done
```

A behaviour can name several cowns and gets them all at once, so there are no locks to order and no deadlocks. `fork` starts work and gives a future; `join` waits for futures without holding a thread. Waiting for input, a pipe or a child process doesn't hold a thread either. For pure parallelism, `par (f x, g y)` evaluates both at once and, to the prover, is just the pair.

## Modules and packages

A file is a module (`module name`); `import std.list (sorted)` brings names in. `export` makes a declaration visible; `export abstract` hides a type's constructors, so its invariants are the module's to keep. A package is a directory with a `checkers.json` naming its dependencies (git repositories, by tag); `checkers run` fetches them and records exact versions in `checkers.lock`.

## Tools

- `checkers check|run|build|trust FILE.ck`: the compiler.
- `checkers fmt`: one format for every file.
- `checkers lsp`: the language server: diagnostics as you type (types first, then proofs), hover with signatures and descriptions, go to definition, references, highlighting.
- `checkers doc DIR -o OUT`: a package's documentation, as on this site.

[SPEC.md](https://github.com/iwahbe/checkers/blob/main/SPEC.md) defines the language in full.
