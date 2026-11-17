# Patterns and `match`

A pattern describes the shape of a value and names its parts. Patterns are used by `match`, `let` and lambda parameters.

## Patterns

```text
pattern  ::= cpat { '|' cpat }
cpat     ::= apat '::' cpat
           | Uname { apat }
           | Uname '{' fieldpat { ',' fieldpat } '}'
           | apat
fieldpat ::= lname [ '=' pattern ]
apat     ::= '_' | lname | literal | '-' number | Uname
           | '(' pattern ')' | '(' pattern ',' pattern { ',' pattern } ')'
           | '[' [ pattern { ',' pattern } ] ']'
```

| Pattern | Matches | Binds |
|---|---|---|
| `_` | anything | nothing |
| `x` | anything | `x` to the value |
| `0`, `-1`, `'a'`, `c'é'`, `"one"` | that literal | nothing |
| `None`, `Leaf` | a constructor without fields | nothing |
| `Some x`, `Node l v r` | a constructor, its fields matching the patterns in order | what they bind |
| `x :: rest` | a non-empty list | its first element and the rest |
| `[]`, `[a, b]` | a list of exactly that many elements | what they bind |
| `(a, b)` | a tuple | its components |
| `Point { x, y = py }` | a record | the fields named; `y = p` matches field `y` against `p` |
| `p \| q` | what `p` or `q` matches | the same names, from whichever matched |

A constructor pattern names a constructor of the value's type (E0241 if it is another type's, E0244 if no constructor has that name) and gives a pattern for each of its fields (E0242). A tuple pattern has one pattern per component (E0246). Literal patterns match numbers, bytes, characters and strings; a `match` whose arms are literals ends with an arm that matches the rest.

```checkers
enum Shape
    Circle r : r~Nat
    Square s : s~Nat
    Rect w h : w~Nat, h~Nat

fn first_size s -> n : s~Shape, n~Nat
    match s
        Circle n | Square n -> n
        Rect w _            -> w

fn describe n -> s : n~Int, s~String
    match n
        0  -> "zero"
        -1 -> "minus one"
        _  -> "other"

fn pair_sum xs -> n : xs~List (Int, Int), n~Int
    match xs
        [(a, b)]         -> a + b
        (a, _) :: _ :: _ -> a
        []               -> 0

check first_size (Rect 2 3) == 2
check describe (-1) == "minus one"
check pair_sum [(1, 2)] == 3
```

### Record patterns

`R { a, b = p }` matches a record of type `R`, binding the field `a` to the name `a` and matching the field `b` against `p`. Fields left out are ignored, except that a field holding a resource can't be left out (E0404, [Capabilities](effects.md#resources)). A field that isn't the record's is E0243.

```checkers
record Point
    x~Int
    y~Int

fn manhattan p -> n : p~Point, n~Nat
    let Point { x, y } = p
    (if x < 0 then 0 - x else x) + (if y < 0 then 0 - y else y)

check manhattan (Point 3 (-4)) == 7
```

## `match`

```text
expr ::= 'match' expr NL INDENT { arm } DEDENT
arm  ::= pattern [ 'if' expr ] '->' ( expr NL | NL INDENT block DEDENT )
```

A `match` evaluates its scrutinee, then tries its arms in order: the first arm whose pattern matches, and whose guard (`if e`) is true, is chosen, and its body is the `match`'s value. Every arm's body has the same type.

**What each arm knows.** In an arm, the prover knows that the scrutinee has the shape of the arm's pattern (`xs == x :: rest`), with the invariants of the constructor matched, and that the earlier arms didn't match, and the guard if there is one. A guard is evaluated with the arm's names bound.

```checkers
fn tail_len xs -> n : xs~List Int, n~Nat
    match xs
        []        -> 0
        _ :: rest -> len rest
```

## Which cases a `match` covers

A `match` must handle every value that can reach it, but only those: a case that the facts in scope rule out may be left out. Each case left out is an obligation that it can't happen, proved like any other ([Proofs](proofs.md)). Here the precondition rules out the empty list:

```checkers
fn head xs -> x : xs~List Int, xs != [], x~Int
    match xs
        y :: _ -> y
```

A case that can happen and has no arm is E0240, with an example of a value that reaches it:

```checkers,compile_fail,E0240
fn head xs -> x : xs~List Int, x~Int
    match xs
        y :: _ -> y
```

In a specification (a predicate, an `ensures`, a type) there are no obligations, so a `match` there must cover every case of its type.

The pattern of a `let` or a lambda's parameter is a `match` with one arm, and follows the same rule: it must match every value that can occur there, and may leave out the cases the facts rule out.

```checkers
fn first xs -> x : xs~List a, len xs > 0, x~a
    let y :: _ = xs
    y
```

**Arms that never run** are warnings, not errors: an arm whose pattern the earlier arms already cover (W021), and an arm or `if` branch where the facts in scope contradict each other, so no value reaches it (W022).

```checkers
fn sign x -> s : x~Int, s~Int
    match x
        0 -> 0
        _ -> if x > 0 then 1 else 0 - 1
```

## Dependent `match`

When the scrutinee is a variable that the expected type mentions, each arm is checked against that type with the variable replaced by the arm's pattern. This is what lets a function return values of different types depending on an argument:

```checkers
enum Kind
    Number
    Text

fn default_of k -> v : k~Kind, v~value_type k
    match k
        Number -> 0
        Text   -> ""

fn value_type k -> t : k~Kind, t~Type
    match k
        Number -> Int
        Text   -> String

check default_of Text == ""
```
