# Types and constraints

Checkers is dependently typed: a type can mention values (`Vec a n`, a list of length `n`), a type can carry a condition its values satisfy (`n~Nat, n < 256`), and the compiler proves each condition where a value must meet one. Types are written in one place only, constraint lists, and most of what a program says about its values is a constraint.

## Constraint lists

```text
constraints ::= constraint { ',' constraint }
constraint  ::= lname '~' [ 'ghost' | 'own' | 'comptime' ] type
              | lname ':' expr
              | expr
```

A constraint list follows `:` in a function's or lemma's signature, a constructor, a class's or instance's header, and makes up a record field's line and a type alias. Each constraint is one of:

| Constraint | Meaning |
|---|---|
| `x~T` | `x` has type `T` |
| `x~ghost T` | `x` exists only in specifications, and is erased ([ghost](#ghost)) |
| `x~own T` | `x` is used exactly once ([own](#own)) |
| `x~comptime T` | `x` is known when compiling ([Staging](staging.md)) |
| a `Bool` expression | a predicate: a precondition, postcondition or invariant |
| `name: e` | a named predicate, used by name ([Proofs](proofs.md#forall)) |
| `C t` | a class constraint ([Classes](classes.md)) |

In a function's signature, a predicate that mentions only parameters is a **precondition**; one that mentions the result is a **postcondition**. Each predicate may rely on those before it: a call in a later predicate must meet its callee's preconditions given the earlier ones.

```checkers
fn clamp lo hi x -> r : lo~Int, hi~Int, lo <= hi, x~Int,
                        r~Int, lo <= r, r <= hi
    if x < lo then lo else if x > hi then hi else x
```

### Two namespaces

After `~`, a `Uname` names a type; anywhere else it names a constructor or a constant. So a type and a constructor may share a name (a record's constructor always does), and `enum Json` may have a constructor `Bool b : b~Bool`. Lowercase names have one namespace, shared by values and types, which is what lets a type mention a value (`p~Parsed Json src i`).

## Built-in types

These are in the prelude, available in every module.

| Type | Values |
|---|---|
| `Bool` | `True`, `False` |
| `Unit` | `()`, the one value; the result of a function with no result to give |
| `Int` | integers of any size |
| `Nat` | `n~Int, n >= 0` |
| `U8`, `U16`, `U32`, `U64` | `Nat`s below 2^8, 2^16, 2^32 and 2^64 |
| `I8`, `I32`, `I64` | `Int`s from -2^(k-1) to 2^(k-1) - 1, for k = 8, 32, 64 |
| `Char` | a Unicode scalar value: a `Nat` up to 0x10FFFF, not a surrogate |
| `String` | text: a sequence of bytes that is valid UTF-8 |
| `Array a` | a sequence of `a`s, indexed from 0 |
| `Bytes` | `Array U8` |
| `List a` | `[]`, or `x :: rest` |
| `Option a` | `None`, or `Some x` |
| `Result a e` | `Ok x`, or `Err e` |
| `(a, b, …)` | tuples of two or more values |
| `a -> b` | functions ([Function types](#function-types)) |
| `Type` | types themselves |

All values are immutable. `Ord` and `Functor`, the prelude's classes, are in [Classes](classes.md#the-prelude-s-classes).

### Numbers

`Int` and `Nat` have no fixed size: arithmetic never overflows and never wraps. The fixed-width types are not separate number systems but refinements of `Int` (and of `Nat`, the unsigned ones), so they mix freely with each other and with `Int`; staying in range is something the compiler proves, not something that is checked at run time or that wraps.

```checkers
fn next b -> n : b~U8, n~Nat
    b + 1

fn byte n -> b : n~Nat, n < 256, b~U8
    n

check next 255 == 256
```

**Arithmetic.** `+ - * / %` take two numbers. The result of `+`, `*`, `/` and `%` on `Nat`s is a `Nat`; on anything else, an `Int`. `a - b` on `Nat`s is a `Nat` too, and needs `a >= b` to be proven (an obligation); on `Int`s it needs nothing. Division and remainder are Euclidean: the remainder is never negative (`-7 / 2 == -4`, `-7 % 2 == 1`), and the divisor must be proven non-zero.

```checkers,compile_fail,E0450
fn under a b -> c : a~Nat, b~Nat, c~Nat
    a - b
```

**Ranges.** Where each operand's bounds are constants, from a literal or from a type such as `U8`, the result keeps them: for a `U8` `x`, `x + 1` has type `(n~Nat, 1 <= n, n <= 256)`. Multiplication takes the extreme products, `%` by a constant `c` gives `0` to `c - 1`, and a bound that isn't a constant is dropped. The branches of an `if` whose type is inferred get the smallest range holding both. Ranges are what let `x % 16` be stored in a byte ([Arrays](#arrays)).

**Literals** take their type from where they are used, and are `Nat` when nothing decides. A number literal where something other than a number is expected is a type error.

### Text

A `String` is UTF-8 text; it can't hold invalid UTF-8. `len s` is its length in **bytes**, and `string.bytes s` gives those bytes. A `Char` is one Unicode scalar value, written `c'é'`; a byte literal `'a'` is a `U8`. Joining strings is `++`.

```checkers
check len "é" == 2
check "ab" ++ "c" == "abc"
```

### Arrays

`Array a` is an immutable sequence with constant-time length and indexing. `len a` is its length; `a[i]` is its element `i` and needs `i < len a` proven (indices are `Nat`s, so `i >= 0` is given). `a ++ b` joins two arrays. `std.array` builds and transforms them (`from_list`, `init`, `map`, `set`, `slice`, …).

`Bytes` is `Array U8`, written `b"…"`. Arrays of fixed-width numbers (`U8`, `I32`, `U64`, …), of `Char`s and of `Bool`s are stored packed, one to eight bytes per element; any other element takes a machine word.

```checkers
import std.array

fn last xs -> x : xs~Array Int, len xs > 0, x~Int
    xs[len xs - 1]

check last (array.from_list [1, 2, 3]) == 3
check b"hi"[0] == 'h'
```

### Lists

`List a` is a linked list: `[]` is the empty list, `x :: rest` a list starting with `x`, and `[1, 2, 3]` is `1 :: 2 :: 3 :: []`. `len xs` and `xs ++ ys` work on lists too. Lists are taken apart with `match`; `std.list` has the usual functions with their proofs.

### `Option` and `Result`

`Option a` is `None` or `Some x`; `Result a e` is `Ok x` or `Err e`. Both work with `try` ([Expressions](expressions.md#try)). They are ordinary enums of the prelude.

### Tuples

`(a, b)` is a pair, `(a, b, c)` a triple, and so on; `()` is `Unit`. A tuple is taken apart with a pattern: `let (x, y) = p`. There is no one-element tuple: `(e)` is just `e`.

A tuple of more than two is a pair whose second part is the rest: `(a, b, c)` and `(a, (b, c))` are the same type, and `(1, (2, 3)) == (1, 2, 3)`. So a pattern may take a tuple apart into fewer parts, its last part the rest, and a function over `(a, t)` accepts a tuple of any length. Laid out in memory, a tuple is one block of its parts, however it was built.

```checkers
fn rest p -> r : p~(a, b, c), r~(b, c)
    let (_, more) = p
    more

check rest (1, 2, 3) == (2, 3)
check (1, (2, 3)) == (1, 2, 3)
```

## Function types

`a -> b` is the type of functions from `a` to `b`. `->` associates to the right: `a -> b -> c` takes an `a` and gives a function from `b` to `c`, which is how every function of several parameters is typed. Inside a constraint list, a function type is written in parentheses: `f~(Int -> Bool)`.

A function type may name its parameter and result and constrain them, like a signature:

```text
'(' [ lname '~' ] type '->' [ lname '~' ] type { ',' expr } ')'
```

Predicates that mention only the parameter are preconditions; the others postconditions.

```checkers
type Big = n~Int, n >= 5

fn apply f x -> r : f~(x~Int -> y~Int, x >= 5, y >= 0), x~Big, r~Int, r >= 0
    f x

fn sub5 x -> y : x~Int, x >= 5, y~Int, y >= 0
    x - 5

check apply sub5 7 == 2
check apply (\x -> x - 5) 6 == 1
```

Calling such a function obliges its preconditions, and gives its postconditions as facts about the result. Passing a function where a refined function type is expected obliges two things, both proved by the compiler: the expected precondition implies the function's own, and the function's postcondition (given the expected precondition) implies the expected one.

**Partial application.** Applying a function to some of its arguments gives a function of the rest, whose preconditions and postconditions are the original's with the given arguments filled in. So `at_least 5`, for `fn at_least k x : x >= k, …`, can be passed wherever a function on numbers of at least 5 is expected.

## Refinements

A refinement is a type with a condition: `(n~Int, n >= 5)`, the `Int`s that are at least 5. It can be named with an alias (`type Big = n~Int, n >= 5`) or written in place, in parentheses; the two are the same type, and refinements are compared by what they imply, not by name.

**Gaining a refinement** is an obligation: a value checked against `Big` must be proven at least 5, where it is passed, returned or built. **Losing one** is free: a `Big` is an `Int`, and a `Nat` is an `Int`.

```checkers
type Small = n~Nat, n < 10

fn digit n -> d : n~Nat, d~Small
    n % 10

fn as_int d -> i : d~Small, i~Int
    d
```

### Refinements inside types

A refinement inside another type means the same thing: every element of a `List Small` is less than 10, and the prover assumes so. A value gains it where it is built: each element of a list literal, each `x` in `x :: rest`, the result of a lambda passed to `list.map`.

Losing it is free and **weakening** it is an obligation: a `List (n~Int, n >= 6)` may be used as a `List (n~Int, n >= 5)` once the compiler proves that `n >= 6` implies `n >= 5`. This follows **variance**: an `Option`, `List`, tuple, record or `Result` is covariant in each parameter used only in its fields, a function type is contravariant in its parameter and covariant in its result, and an abstract type is as its polarity marks say ([Modules](modules.md#abstract-types)).

But a refinement is never gained through a type argument of an existing value: a `List Int` can't be used as a `List Nat` (E0262), since that would take a proof about every element. Give the value the refined type where it is built.

```checkers,compile_fail,E0262
fn narrow xs -> ys : xs~List Int, ys~List Nat
    xs
```

## Type parameters

A lowercase name in a type that isn't in scope is a **type parameter**: an implicit argument of the function, filled in at each call from the arguments' types, and erased when the program runs.

```checkers
fn pair x y -> p : x~a, y~b, p~(a, b)
    (x, y)

check pair 1 "one" == (1, "one")
```

A type parameter applied to arguments is a type constructor: in `xs~f Int`, `f` has kind `Type -> Type`, and may be `List`, `Option` or `Array`. Such parameters are usually constrained by a class ([Classes](classes.md#classes-over-type-constructors)).

A name used as a module qualifier (`future` in `future.Future`) is never taken as a type parameter.

## Types that depend on values

A type may mention values: an enum's parameter can be a number (`Vec a n`), and a type can be computed by a function, evaluated while checking. In the standard library, the fields of a spawned process have types computed from how its streams were set up:

```checkers
enum Stream
    Pipe
    Inherit

fn handle s -> t : s~Stream, t~Type
    match s
        Pipe    -> Bytes
        Inherit -> Unit

fn example -> h : h~handle Pipe
    b"output"
```

When a `match` takes apart a variable, each arm is checked with the variable replaced by the arm's pattern in the expected type and in the types of the variables in scope ([Patterns](patterns.md#dependent-match)).

A type computed by a `match` on something unknown may be a resource if one of the `match`'s arms may be one. `proc.pipe_end s` is a `File` for `Pipe` and a `Unit` otherwise, so a value of it is used exactly once, except in an arm of `match s` that makes it a `Unit`.

## Multiplicities

Every variable has a multiplicity: how many times it is used when the program runs.

### `ghost`

A `ghost` variable or field has multiplicity 0: it exists only in specifications. It may appear in types, predicates and proofs, never in code that runs (E0403), and it is erased. Ghost parameters are how a function talks about a value it doesn't need, such as the original list in a specification of an in-place step.

```checkers,compile_fail,E0403
fn bad g x -> y : g~ghost Nat, x~Nat, y~Nat
    g + x
```

Proofs are always ghost: a lemma, a `have`, and every predicate are erased.

### `own`

An `own` variable has multiplicity 1: it is used exactly once on every path. Values that hold resources (open files, child processes) are always used so, whether written `own` or not ([Capabilities and resources](effects.md#resources)). `own` is written on a parameter whose type is a type parameter, `v~own a`, so that a generic function may be given a resource: without it, the function might copy or drop its argument, so passing it a resource is an error. On a type that is a resource already it is redundant (W010); on one that can never be a resource it is an error (E0358). On a function type, `f~own (Unit -> a)`, it promises the function is called exactly once, so it may be given a closure that uses a resource ([One-shot closures](effects.md#one-shot-closures)). On a function type's parameter, `(v~own a -> b)`, it says the function takes its argument once, so it may be given a function that takes a resource; a parameter whose type is a resource is taken once anyway. `ghost` and `comptime` can't be written inside a type, nor `own` anywhere there but on a function type's parameter (E0123).

Every other variable has the default multiplicity: any number of times, including none.

### `comptime`

A `comptime` parameter must be known when the program is compiled; calls with it are expanded while compiling ([Staging](staging.md)).

## The prelude

The prelude is in scope in every module. Besides the types above, it has:

- the function `not` on `Bool`;
- `len e`, the length of a `String` (in bytes), an `Array` or a `List`, and `format e`, any value as text ([Running programs](execution.md#format)): built-in operators written like functions, which must be applied (E0214) and can't be passed as values (write `\x -> len x`);
- the classes `Ord`, `Add`, `Sub`, `Mul`, `Neg`, `Monoid` and `Functor`, with their instances for its types ([Classes](classes.md#the-prelude-s-classes));
- the operators, whose meanings are in [Expressions](expressions.md#operators).
