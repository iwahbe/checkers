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

```checkers,compile_fail,E0450
module wrong

fn last xs -> x : xs~Bytes, x~U8
    xs[len xs - 1]
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

## Cases that can't occur

```checkers
module head

export fn head xs -> r : xs~List Int, xs != [], r~Int
    match xs
        x :: _ -> x
```

A `match` covers the values that can reach it: here the precondition rules out `[]`, and the prover checks that it does. An arm that can never run, like `[] -> 0` here, is a warning, as are functions, constructors and fields that nothing reachable from `main` (or from a library's exports) uses.

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

## Classes and sorting

```checkers
module versions

import std.list (sort, sort_by)

record Version
    major~Nat
    minor~Nat

# An order on versions: by major number, then minor. `Ord`, in the prelude,
# asks for `le` and three lemmas about it (`trans`, `total`, `antisym`);
# Z3 proves them here without help.
instance Ord Version
    fn le v w
        v.major < w.major or (v.major == w.major and v.minor <= w.minor)

# Generic over any type with an order: `Ord a` gives `le` at `a`, and its
# lemmas, used with `have`.
fn larger x y -> r : Ord a, x~a, y~a, r~a, le x r and le y r
    have total x y
    have refl x
    have refl y
    if le x y then y else x

check sort [Version 1 2, Version 0 9, Version 1 0] == [Version 0 9, Version 1 0, Version 1 2]
check larger "fig" "apple" == "fig"

# `sort_by` takes any comparison that orders every two values one way or
# the other: a `forall` it requires, proved where it is called.
check sort_by (\x y -> x >= y) [2, 3, 1] == [3, 2, 1]
```

A class lists functions and lemmas; an instance gives the functions for one type and proves the lemmas (or Z3 does). A function generic over the class (`Ord a`) gets them where it is called, for the caller's type. The prelude's `Ord` has instances for numbers, `Bool`, `String`, `List` and `Option`; `std.list` sorts by it (`sort`), by a key (`sort_as`), or by a comparison (`sort_by`), each proved to give a sorted permutation.

## What a proof rests on

A program that checks is proved by Z3 and by computing at compile time, from two kinds of fact taken without a proof: the standard library's axioms (lemmas whose proof is `__builtin`, facts about functions implemented in the runtime, trusted like that code) and `admit`s. An `admit` is an unproven assumption, allowed while developing; `checkers build --release` refuses a program that relies on one.

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
import std.string (format)
import std.terminal

# A cown owns a value. Behaviours (`when`) that name it run one at a time,
# in the order they were scheduled, and hand back its new value.
export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let hits = cown.new 0 sched
    when n = hits using sched
        n + 1
    when n = hits using sched
        terminal.print_line format"hits: {n}" term
        n
    let a = future.fork sched $ \_ ->
        20
    let b = future.fork sched $ \_ ->
        22
    let (x, y) = future.join (a, b)
    if x + y == 42 then Success else Failure 1
```

A behaviour can name several cowns and gets them all at once, so there are no locks to order and no deadlocks. `future.fork` starts work and gives a future; `future.join` gives a future's value, or a tuple of futures' values, once they are filled, without holding a thread. Waiting for input, a pipe or a child process doesn't hold a thread either. For pure parallelism, `par (f x, g y)` evaluates both at once and, to the prover, is just the pair.

## Modules and packages

A file is a module (`module name`); `import std.list (sorted)` brings names in. `export` makes a declaration visible; `export abstract` hides a type's constructors, so its invariants are the module's to keep. A package is a directory with a `checkers.json` naming its dependencies (git repositories, by tag); `checkers run` fetches them and records exact versions in `checkers.lock`.

## Tools

- `checkers check|run|build FILE.ck`: the compiler.
- `checkers fmt`: one format for every file.
- `checkers lsp`: the language server: diagnostics as you type (types first, then proofs), hover with signatures and descriptions, go to definition, references, highlighting.
- `checkers doc DIR -o OUT`: a package's documentation, as on this site.

The [Reference](reference/index.md) describes the whole language, rule by rule.
