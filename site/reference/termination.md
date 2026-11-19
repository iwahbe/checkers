# Recursion and termination

Every function must be shown to finish for every argument that meets its preconditions, unless it is declared `partial`. This is what makes a function's postcondition trustworthy (a function that never returned could promise anything), and what lets a recursive call assume the function's own postcondition: an induction on the recursion ([Proofs](proofs.md#induction)).

A function finishes if each recursive call (to itself, or to a function it calls that calls it back) is made on something smaller. There are three ways to show it.

## Structural recursion

A call is structurally smaller when an argument is a part of a parameter, taken out of it by a `match`: a list's tail, a tree's subtree. Nothing needs to be written.

```checkers
enum Tree
    Leaf
    Node left value right : left~Tree, value~Int, right~Tree

fn total t -> n : t~Tree, n~Int
    match t
        Leaf         -> 0
        Node l v r   -> total l + v + total r
```

Recursion through a container counts as structural: a function on a tree whose children are in a `List` may call itself on each child, as `list.map depth kids` does, where `kids` is a field of the value being recursed on.

```checkers
import std.list

enum Rose
    Rose label kids : label~String, kids~List Rose

fn depth r -> n : r~Rose, n~Nat
    match r
        Rose _ kids -> 1 + list.max_of (list.map depth kids)
```

## `decreasing`

When the recursion isn't structural, the first line of the body may give a **measure**: `decreasing e`, where `e` is a `Nat`, or a tuple of `Nat`s compared lexicographically (first components first). At every recursive call, the measure at the call's arguments must be smaller than at the function's parameters, given the facts there. Each is an obligation, proved like any other.

```checkers
# The position of the first space at or after `i`.
fn find_space src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, j <= len src
    decreasing len src - i
    if i < len src and src[i] != ' ' then find_space src (i + 1) else i

fn ack m n -> r : m~Nat, n~Nat, r~Nat
    decreasing (m, n)
    if m == 0
        n + 1
    else if n == 0
        ack (m - 1) 1
    else
        ack (m - 1) (ack m (n - 1))
```

Functions that call each other share one measure: each gives its own `decreasing`, and every call between them must make the callee's measure, at the call's arguments, smaller than the caller's at its parameters.

A recursive function used as a value inside its own recursion (passed to another function rather than called) can't be checked (E0303).

## Guessed measures

A function whose recursion isn't structural and that has no `decreasing` gets a measure guessed by the compiler, which checks it as if it had been written. The candidates are, for each parameter, its size (a number itself, the length of a list, array, string or bytes), the distance each comparison guarding a recursive call bounds (`i < len src` gives `len src - i`, `x < 0` gives `0 - x`), and the sum of two parameters' sizes; each alone, then pairs compared lexicographically. The first that every recursive call makes smaller is the measure, and the trust ledger names it.

```checkers
fn fib n -> r : n~Nat, r~Nat
    if n < 2 then n else fib (n - 1) + fib (n - 2)

fn count_up i n -> r : i~Nat, n~Nat, r~Nat
    if i < n then count_up (i + 1) n else i
```

If none works, the error (E0301) names the measures tried and, for each, a call it couldn't be shown smaller at:

```checkers,compile_fail,E0301
fn collatz n -> r : n~Nat, r~Nat
    if n <= 1 then 0 else if n % 2 == 0 then 1 + collatz (n / 2) else 1 + collatz (3 * n + 1)
```

## `partial`

A function declared `partial fn` need not finish: a server's loop, an interpreter, `collatz`. It is checked like any other function, except for termination. A function that isn't partial can't call a partial one (E0302), and specifications and proofs can't mention one, so nothing that is proved depends on code that may not finish. `main` may be `partial`.

```checkers
partial fn collatz n -> r : n~Nat, r~Nat
    if n <= 1 then 0 else if n % 2 == 0 then 1 + collatz (n / 2) else 1 + collatz (3 * n + 1)
```

## Lemmas

A lemma that uses itself is a proof by induction, and must terminate the same way: structurally, with `decreasing` on the first line of its body (before its `let`s and `ensures`), or with a measure guessed as for a function ([Proofs](proofs.md#induction)). A lemma about a function that recurses on a position is proved by induction on the same measure:

```checkers
fn walk n x -> r : n~Nat, x~Nat, x <= n, r~Nat
    if x < n then walk n (x + 1) else x

lemma walk_end n x : n~Nat, x~Nat, x <= n
    decreasing n - x
    ensures walk n x == n
    proof
        if x < n then have walk_end n (x + 1) else auto
```

Without the `decreasing` line, `n - x` would be guessed from the guard `x < n`.
