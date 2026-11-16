# Declarations

A module's body is a sequence of declarations:

```text
decl      ::= [ 'export' [ 'abstract' | 'transparent' ] ] decl_body | check | instance
decl_body ::= fn | enum | record | alias | const | lemma | class
```

Each name is declared once per module (E0350). Exports are described in [Modules](modules.md#exports), lemmas in [Proofs](proofs.md#lemmas), classes and instances in [Classes](classes.md).

## Order

The order of declarations in a file doesn't matter: they are checked in the order of what they use, and each may use any other that doesn't depend on it. Function bodies may call one another freely, so mutual recursion needs nothing special. What can't be circular is a declaration's **head**: a type's constructors, a constant's value, a function's or lemma's signature. A head that needs itself through any chain of declarations is E0225:

```checkers,compile_fail,E0225
let A = B + 1
let B = A
```

Types may refer to one another (a tree and a forest of trees), but only through an `enum` or a `record`: a type alias that needs itself through aliases alone would never finish unfolding, which is E0225 too.

## Functions

```text
fn ::= [ 'partial' ] 'fn' lname { lname } [ '->' lname ] [ ':' constraints ] NL
       INDENT [ 'decreasing' expr NL ] block DEDENT
```

A function has a name, parameters, optionally a name for its result, and a **signature**: the constraints after `:` ([Types and constraints](types.md)). They give each parameter's type (`x~Int`), the result's type (`r~Int`), preconditions (predicates about the parameters) and postconditions (predicates that mention the result). The body is an indented [block](expressions.md#blocks) whose value is the result.

```checkers
# The integer square root: the largest `r` with `r * r <= n`.
fn isqrt n -> r : n~Nat, r~Nat, r * r <= n, n < (r + 1) * (r + 1)
    decreasing n
    if n < 2
        n
    else
        let s = isqrt (n / 4) * 2
        if (s + 1) * (s + 1) <= n then s + 1 else s

check isqrt 17 == 4
```

Inside the body the preconditions are facts, and the body must make every postcondition true: each is an obligation ([Proofs](proofs.md)). At each call, the preconditions are obligations about the arguments, and the postconditions become facts about the result.

**Types that can be left out.** A constraint is needed only where the type can't be worked out. A parameter's type must be given (E0203 if it can't be inferred), but the result's may be left out, along with the `->` name, when the body settles it:

```checkers
fn is_space b : b~U8
    b == ' '

fn add x y : x~Int, y~Int
    x + y

check is_space ' '
check add 1 2 == 3
```

A result type that isn't written is one type for every call: it may be a type parameter, but it can't depend on the arguments' values. A result type that does is written.

**Generic functions.** A lowercase name in a type that isn't a parameter, a local or a declaration is a type parameter of the function: `fn first xs : xs~List a` is generic in `a` ([Types](types.md#type-parameters)).

**`partial`.** Every function must be shown to terminate ([Recursion and termination](termination.md)), unless it is declared `partial`. A partial function can't be called from a function that isn't partial (E0302), nor from a specification, so a proof never depends on code that may not finish.

**`decreasing e`**, on the first line of a body, gives the measure that proves the recursion ends ([Termination](termination.md#decreasing)).

**Builtins.** A body that is `__builtin` alone marks a function the runtime implements. Only the standard library may declare one (E0356).

## Enums

An enum is a type whose values are made by one of several constructors:

```text
enum ::= 'enum' Uname { param } [ ':' constraints ] NL INDENT { ctor NL } DEDENT
ctor ::= Uname { lname } [ ':' constraints ]
```

```checkers
enum Shape
    Circle r      : r~Nat
    Rect w h      : w~Nat, h~Nat
    Empty

fn area s -> a : s~Shape, a~Nat
    match s
        Circle r -> 3 * r * r
        Rect w h -> w * h
        Empty    -> 0

check area (Rect 2 3) == 6
```

A constructor's fields are named and given types in its constraint list; every field needs a type (E0352). A constructor is applied to its fields in order, like a function (`Rect 2 3`), and is a function value when partly applied. Values are taken apart with `match` ([Patterns](patterns.md)).

**Type parameters** follow the name; a parameter with no constraint is a type. An enum may refer to itself in its fields (a recursive type), but only in positive places: never to the left of an `->` in its own fields (E0354).

```checkers
enum Tree a
    Leaf
    Node left value right : left~Tree a, value~a, right~Tree a

fn size t -> n : t~Tree a, n~Nat
    match t
        Leaf         -> 0
        Node l _ r   -> size l + 1 + size r

check size (Node Leaf 'x' (Node Leaf 'y' Leaf)) == 2
```

**Invariants.** A predicate in a constructor's constraint list is part of the type: building the value is an obligation that it holds, and matching on the value gives it as a fact.

```checkers
enum Range
    Span lo hi : lo~Int, hi~Int, lo <= hi

fn width r -> w : r~Range, w~Nat
    match r
        Span lo hi -> hi - lo
```

**Indexed families.** A type parameter may be a value, constrained by each constructor with equations. Here `n` is the length, and a `Vec a 0` can only be `Nil`:

```checkers
enum Vec a n : a~Type, n~Nat
    Nil         : n == 0
    Cons x rest : x~a, rest~Vec a m, n == m + 1

fn head v -> x : v~Vec a n, n > 0, x~a
    match v
        Cons x _ -> x
```

`m` in `Cons`'s constraints is not a field: a lowercase name that is neither a parameter nor a field is bound implicitly, and erased.

## Records

A record is a type with one constructor, named like the type, whose fields are listed one per line:

```text
record ::= 'record' Uname { param } [ ':' constraints ] NL INDENT { field NL } DEDENT
field  ::= lname '~' [ 'ghost' ] expr { ',' expr }
```

```checkers
record Interval
    lo~Int
    hi~Int, lo <= hi

fn length i -> n : i~Interval, n~Nat
    i.hi - i.lo

check length (Interval 2 5) == 3
```

A record is built by applying its name to the fields in order (`Interval 2 5`). A field is read with a glued `.` (`i.hi`) and the fields are taken apart with a record pattern ([Patterns](patterns.md#record-patterns)). Each field's line may add predicates after its type, which are invariants as for an enum's constructor; a predicate may mention the fields before it. A field declared `ghost` exists only for specifications: it is erased when the program runs ([Types](types.md#ghost)).

In type positions (after `~`) a record's name is the type; elsewhere it is the constructor. The two can't be confused: types are written only after `~` ([Types](types.md#two-namespaces)).

## Type aliases

```text
alias ::= 'type' Uname { lname } '=' constraints NL
```

An alias names a type, often a refinement of another: the first constraint gives a name and a base type, and the rest are predicates about it (E0106 if the first isn't a typing, E0351 if a later one is).

```checkers
type Percent = n~Nat, n <= 100

type Pairs a = xs~List (a, a)

fn half p -> q : p~Percent, q~Percent
    p / 2
```

An alias stands for its definition: `Percent` and `(n~Nat, n <= 100)` are the same type ([Refinements](types.md#refinements)). An alias's parameters are types.

## Constants

```text
const ::= 'let' Uname '=' expr NL
```

A top-level `let` names a value computed once. Its name is a `Uname`, conventionally `SCREAMING_SNAKE_CASE`. Its type is that of the expression, and the prover knows its value.

```checkers
let ORIGIN = (0, 0)
let PRIMES = [2, 3, 5, 7, 11]

check PRIMES != []
```

## `check`

```text
check ::= 'check' expr NL
```

A `check` is a test that runs when the module is compiled: the expression, a `Bool`, is evaluated, and the program doesn't compile if it is `False` (E0260) or stops with a run-time error (E0261). A `check` gets no capabilities, so it can't have effects.

```checkers,compile_fail,E0260
fn double x -> y : x~Int, y~Int
    x + x

check double 2 == 5
```

When a `check` fails, the error shows the two sides of a comparison. A `check` that holds is recorded in the trust ledger as proved by evaluation ([Proofs](proofs.md#the-trust-ledger)).
