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

Recursion through a container counts as structural when the function it goes through calls its function argument only with elements of the list. Each element of a list that is part of a parameter is itself a part of it, so a function on a tree whose children are in a `List` may pass itself to `list.map` with the children. The function passed may be the function's name, a partial application of it (`list.map (depth_from k) kids`: `kids`' elements are its next argument), or a lambda (`list.all (\k -> ok k) kids`: `k` is the part).

Where that function's body is visible, as it is for proofs (in the same module, or exported `transparent`), its body shows it: every use of its function parameter is a call on a part of the list, or passes the parameter on to a function that keeps the same promise.

```checkers
import std.list

enum Rose
    Rose label kids : label~String, kids~List Rose

fn depth r -> n : r~Rose, n~Nat
    match r
        Rose _ kids -> 1 + list.max_of (list.map depth kids)

# `every` calls `p` only with elements of `xs`, as its body shows.
fn every xs p -> r : xs~List a, p~(a -> Bool), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and every rest p

fn labelled r -> b : r~Rose, b~Bool
    match r
        Rose label kids -> label != "" and every kids labelled
```

A sealed function of another module makes the promise in its signature instead, so that changing its body never breaks an importer: its function parameter's precondition says the argument is in the container, as `list.all`'s `p~(x~a -> Bool, list.contains xs x)` does (`list.all` is exported `transparent`, and makes the promise anyway). Any membership works, `list.contains` or a container's own, as long as its body is visible (in the same module, or exported `transparent`) and shows it is true only of something equal to a part of the container. The function's body must keep the promise, which is proved like any precondition.

```checkers
import std.list

export fn each xs p -> r : xs~List a, p~(x~a -> Bool, list.contains xs x), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and each rest p
```

Without either, a call through it is E0301.

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

A function whose recursion isn't structural and that has no `decreasing` gets a measure guessed by the compiler, which checks it as if it had been written. The candidates are, for each parameter, its size (a number itself, the length of a list, array, string or bytes), the distance each comparison guarding a recursive call bounds (`i < len src` gives `len src - i`, `x < 0` gives `0 - x`), and the sum of two parameters' sizes; each alone, then pairs compared lexicographically. The first that every recursive call makes smaller is the measure. A parameter taken apart with `[]` and `x :: rest` at a type other than a list ([sequence patterns](patterns.md#sequence-patterns)) has `Seq.size` of it among the candidates: `uncons` promises that the rest is smaller.

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

A lemma that uses itself is a proof by induction, and must terminate the same way: structurally, with `decreasing` on the first line of its proof (the measure is part of the proof), or with a measure guessed as for a function ([Proofs](proofs.md#induction)). A lemma about a function that recurses on a position is proved by induction on the same measure:

```checkers
fn walk n x -> r : n~Nat, x~Nat, x <= n, r~Nat
    if x < n then walk n (x + 1) else x

lemma walk_end n x : n~Nat, x~Nat, x <= n
    ensures walk n x == n
    proof
        decreasing n - x
        if x < n then have walk_end n (x + 1) else auto
```

Without the `decreasing` line, `n - x` would be guessed from the guard `x < n`. An instance's lemma gives its measure the same way, on the first line of its proof.
