# Proofs

The compiler proves a program's conditions before it runs: every index in bounds, every `Nat` subtraction non-negative, every divisor non-zero, every precondition at every call, every postcondition, every invariant. Each such condition is an **obligation**. The compiler hands it to the Z3 theorem prover, together with the facts known where it arises; a program with an obligation that can't be proved doesn't compile. Where Z3 needs help, the program says what to use: a fact (`have`), or a lemma proved separately.

## Obligations

| Obligation | Where it arises | What must hold |
|---|---|---|
| precondition | each call of a function with preconditions | the preconditions, with the arguments in place of the parameters |
| postcondition | each value a function body can return | the postconditions, with that value as the result |
| invariant | each constructor application | the constructor's predicates, and its fields' refinements |
| refinement | a value used where a refined type is expected (a `U8`, `Big`, an element of a `List Small`) | the refinement's predicates, of the value |
| weakened refinement | a value of a refined type used at a weaker one inside another type ([Types](types.md#refinements-inside-types)) | the found predicates imply the expected ones |
| function value | a function passed where a refined function type is expected | the expected precondition implies the function's, and its postcondition the expected one |
| `Nat` subtraction | `a - b` on `Nat`s | `a >= b` |
| division | `a / b`, `a % b` | `b != 0` |
| index | `a[i]` | `i < len a` |
| termination | each recursive call ([Termination](termination.md)) | the measure gets smaller |
| case left out | each case a `match` doesn't handle ([Patterns](patterns.md#which-cases-a-match-covers)) | the case can't occur |
| cown invariant | each value a behaviour hands back to a cown of a refined type ([Concurrency](concurrency.md#invariants)) | the refinement |
| lemma | a lemma without a proof, or `auto` in a proof | its conclusion, or the goal |
| `have e` | a `have` of a `Bool` | `e` |

A `check` is not proved but evaluated ([Declarations](declarations.md#check)).

Each obligation is reported at its own place. When one fails, E0450 shows what couldn't be proved, the facts it was proved from, and, when Z3 finds one, a **counterexample**: values of the variables that satisfy every fact and break the obligation.

```checkers,compile_fail,E0450
fn last xs -> x : xs~Bytes, x~U8
    xs[len xs - 1]
```

## Facts in scope

At each point of a function, the prover may assume:

- the function's **preconditions**;
- each variable's **type**: `n >= 0` for a `Nat`, `n < 256` for a `U8`, the predicates of any refinement, and the invariants of a value's constructor, with its type's value parameters filled in;
- the **definition** of each `let`-bound variable;
- the **path conditions**: the condition of each enclosing `if` (true in its `then`, false in its `else`), the left operand of an enclosing `and`, `or` or `implies` when the right one is evaluated, and in a `match` arm the equation of the arm's pattern (`xs == y :: rest`), the invariants of the constructor matched, the guard, and the failure of the earlier arms;
- each fact added with `have`, and the conclusion of each lemma brought in with `have`;
- the **postconditions** of every function called in the obligation or in these facts, at the arguments it is called with. This includes a recursive call of the function being checked, which is how a recursive function proves its own postcondition ([Induction](#induction)).

```checkers
fn max_of xs -> m : xs~List Int, xs != [], m~Int
    match xs
        [x]       -> x
        x :: rest -> if x > max_of rest then x else max_of rest
```

## What the prover knows

**Functions of the same module** are known by their definitions: Z3 unfolds a function's body where a proof needs it, so a postcondition can be proved by computing. A recursive definition is unfolded only where its recursion is known to end.

**Functions of other modules** are sealed ([Modules](modules.md#sealing)): Z3 knows only their postconditions. A library therefore exports, as postconditions and lemmas, the facts its users need. A function exported `transparent` is known by its definition everywhere.

**Constants** are known by their value. A constant array's length and elements are known as facts.

**Values.** Numbers are Z3's integers; `String`s are their UTF-8 bytes, so `len`, `++` and encoding are exact; `Array`s and `Bytes` are sequences; enums, records, lists and tuples are datatypes; function values are functions Z3 can apply, and a lambda is known by its body.

**Outside what Z3 handles**: behaviours (`when`, `fork`, `join`) and polymorphic function values. An obligation that needs one is E0451; state what is needed as a lemma instead.

Z3 is limited by an amount of work, not by time, so whether an obligation is proved doesn't depend on the machine; and its answers are cached, so checking unchanged code again is fast.

## `have`

```text
stmt ::= 'have' expr
```

`have` adds a fact, in a function body or a proof. It has no effect when the program runs.

- **`have e`**, `e` a `Bool`: `e` is an obligation, proved from the facts so far, and then a fact.
- **`have l a b`**, `l` a lemma applied to all its arguments (E0454 otherwise): the lemma's preconditions at those arguments are obligations, and its conclusion at them is a fact.

`have` is how a proof points Z3 at what it needs: Z3 isn't given every lemma, only those a `have` names.

```checkers
import std.list (perm, perm_middle)

# `perm_middle`, a lemma of `std.list`: moving an element to the front gives
# a permutation.
fn moved xs y ys -> b : xs~List Int, y~Int, ys~List Int, b~Bool, b
    have perm_middle xs y ys
    perm (xs ++ (y :: ys)) (y :: (xs ++ ys))
```

## Lemmas

```text
lemma ::= 'lemma' lname { lname } [ ':' constraints ] NL INDENT
          { 'let' pattern '=' expr NL } 'ensures' expr NL
          [ 'proof' NL INDENT block DEDENT ] DEDENT
```

A lemma states a fact for all values of its parameters that satisfy its preconditions: its conclusion follows `ensures`. `let` lines before `ensures` name parts of the statement. Without a `proof`, Z3 proves the conclusion from the preconditions. A lemma is used with `have`, and is erased: it never runs.

```checkers
fn double n -> m : n~Nat, m~Nat
    n + n

lemma double_even n : n~Nat
    ensures double n % 2 == 0
```

**Proofs.** A `proof` block is code that is checked but never run: its statements are `have`s and `let`s, and `match` and `if` split the proof into cases, each proved separately. The block's last line, in each case, is `auto` (prove the goal from the facts), `admit` (assume it, recorded in the trust ledger), or a `have`, after which the goal is proved as by `auto`.

### Induction

A lemma that uses itself is a proof by induction: the recursive `have` gives the conclusion for a smaller argument. Like a recursive function it must terminate, so the argument must be structurally smaller or the lemma must give `decreasing` ([Termination](termination.md)).

```checkers
fn sum xs -> n : xs~List Nat, n~Nat
    match xs
        []        -> 0
        x :: rest -> x + sum rest

lemma sum_append xs ys : xs~List Nat, ys~List Nat
    ensures sum (xs ++ ys) == sum xs + sum ys
    proof
        match xs
            []        -> auto
            _ :: rest -> have sum_append rest ys
```

A recursive function proves its postcondition the same way: each recursive call may assume the postcondition for its arguments.

## `forall`

```text
constraint ::= lname ':' expr
expr       ::= 'forall' lname { lname } ':' constraints
```

A precondition may be named, `name: e`, and then a named precondition may state something of all values: `forall x y : x~a, y~a, le x y or le y x`. Its clauses are typings for its variables, then the predicates that follow and mention one of them; the last is its conclusion. A `forall` may appear only in a named precondition or in a lemma's `ensures` (E0289), in a positive place: the whole condition, a side of `and` or `or`, the right side of `implies`, or another `forall`'s conclusion.

- **At a call**, it is an obligation, proved for fresh, arbitrary values of its variables.
- **In the body**, it is not given to Z3 as it stands. `have name a b` gives what it says of the values `a`, `b`, filled in for its variables left to right (E0290 if the count doesn't match).
- **A lemma** may conclude a `forall`. In its `proof` the variables are in scope by name and the premises are facts. `have l x` with the lemma's own arguments brings the `forall` into scope; adding values for its variables fills them in.

```checkers
fn max_by le x y -> r : le~(a -> a -> Bool), x~a, y~a,
                        total: forall p q : p~a, q~a, le p q or le q p,
                        r~a, le x r, le y r
    have total x y
    have total x x
    have total y y
    if le x y then y else x

check max_by (\a b -> a <= b) 3 5 == 5
```

## The trust ledger

Every module records what its proofs rest on: each obligation proved by Z3, each `check` and each fact proved by evaluating closed values, each axiom of the standard library and each `admit`. `checkers trust FILE.ck` prints it, with a summary for each module the program loads and the standard library's builtins the program uses.

- **`admit`** assumes a goal without proof. It is allowed while developing; `checkers build --release` refuses a program that relies on one (E0455).
- **Axioms** are lemmas of the standard library whose proof is `__builtin`: facts about functions implemented in the runtime, trusted like that code.

What the compiler trusts is its own parts: the parser and type checker, the translation of obligations for Z3, Z3, the code generator and runtime, and the standard library's axioms and builtins.
