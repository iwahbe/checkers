# Expressions

Checkers is expression-oriented: a function's body, an `if`, a `match` and a block each have a value. There are no statements apart from those inside blocks, no assignment and no loops: repetition is recursion ([Recursion and termination](termination.md)), and data is never changed in place.

## Blocks

A block is a sequence of lines at one indentation; its last line is its value.

```text
block ::= { stmt NL } expr NL
stmt  ::= 'let' pattern '=' ( expr | NL INDENT block DEDENT )
        | 'have' expr
        | expr
        | pattern '<-' expr
        | when | fork | join
```

**`let`** evaluates an expression and binds the pattern on its left to it, for the rest of the block. A `let` whose expression starts on the next line takes an indented block. The pattern must match every value of the type ([Patterns](patterns.md)): `let (q, r) = p` takes a tuple apart.

```checkers
fn area w h -> a : w~Nat, h~Nat, a~Nat
    let (x, y) = (w + 1, h + 1)
    let inner =
        let s = x * y
        s - 1
    inner + 1
```

A name bound by `let` hides an earlier one of the same name for the rest of the block.

**A line that is just an expression** must be a call that returns `Unit`, such as printing a line; its value is thrown away. Any other value on a line of its own is an error (E0215); write `let _ = e` to discard it on purpose.

**`have`** adds a fact for the prover ([Proofs](proofs.md#have)); it has no effect when the program runs. **`<-`** binds the results of an operation on a resource ([Capabilities](effects.md#resources)). **`when`**, **`fork`** and **`join`** schedule concurrent work ([Concurrency](concurrency.md)).

## Names and literals

A lowercase name is a local (a parameter, a `let`, a pattern variable) or a function; an uppercase one is a constructor or a constant. `q.n` is the export `n` of the module imported as `q`. Literals are described in [Lexical structure](lexical.md#literals).

## Application

A function is applied by writing its arguments after it, separated by spaces: `f x y`. Application associates to the left, so `f x y` is `(f x) y`: every function takes its parameters one at a time, and applying it to fewer than all of them gives a function of the rest. Constructors are applied the same way (`Some x`, `Rect 2 3`).

Application binds tighter than every operator except a glued `.` and `[` ([Lexical structure](lexical.md#glued-and-spaced-and)): `f x + g y` is `(f x) + (g y)`, and `f p.x` is `f (p.x)`. An argument that is itself an application, an operator expression, an `if`, a `match`, a lambda or a `try` needs parentheses, or `$`.

As in Haskell, `f -1` is a subtraction, `f - 1`; pass a negative number as `f (-1)`.

## Operators

From highest precedence to lowest:

| Operators | Associativity | Meaning |
|---|---|---|
| glued `.name`, `[i]` | left | field, qualified name, index |
| application | left | |
| `.` (spaced) | right | composition: `(f . g) x == f (g x)` |
| `-` (prefix) | | negation |
| `*` `/` `%` | left | multiplication, Euclidean division and remainder |
| `+` `-` `++` | left | addition, subtraction, joining |
| `::` | right | a list's first element and the rest |
| `==` `!=` `<` `<=` `>` `>=` | none | comparison |
| `and` | right | conjunction, short-circuit |
| `or` | right | disjunction, short-circuit |
| `implies` | right | implication, short-circuit: `a implies b` is `not a or b` |
| `->` | right | function type, in a type |
| `$` | right | application with the lowest precedence: `f $ g x` is `f (g x)` |

**Arithmetic** is on numbers, with the types and obligations given in [Types](types.md#numbers): `a - b` on `Nat`s needs `a >= b`, `/` and `%` need a non-zero divisor. On other types the arithmetic operators and comparisons work through classes ([Classes](classes.md#operators)); without an instance they are E0210.

**`++`** joins two `String`s, two `Array`s (and `Bytes`) or two `List`s of the same type.

**Comparisons** can't be chained: `a < b < c` is E0109; write `a < b and b < c`. `<`, `<=`, `>`, `>=` compare numbers, and any type with an `Ord` instance.

**Equality.** `==` and `!=` compare two values of the same type structurally: numbers, strings, bytes, arrays, and enums, records, lists and tuples whose parts compare. In code that runs, a function, a capability, a cown, a future, a file or a process handle can't be compared, nor can a value that contains one (E0263); a generic function that compares values of its type parameter can't be given such a type (E0264). In specifications (predicates, invariants, lemmas) `==` is logical equality and works on every type.

```checkers,compile_fail,E0263
fn same f g -> b : f~(Int -> Int), g~(Int -> Int), b~Bool
    f == g
```

**`and`, `or`, `implies`** evaluate their right operand only if it can change the result. The prover knows this: in `i < len xs and xs[i] == 0`, the index is in bounds because the right side runs only when the left is true.

**Operators as functions.** In parentheses, an operator is a function of two arguments, `(+) 1 2 == 3`, and with one operand it is a section: `(+ 1)` adds one, `(10 -)` subtracts from ten.

```checkers
import std.list

fn inc x -> y : x~Int, y~Int
    x + 1

check (inc . inc) 0 == 2
check list.map (* 2) [1, 2, 3] == [2, 4, 6]
check (list.length $ list.reverse [1, 2]) == 2
check (10 - 3) * 2 == 14
```

## `if`

```text
expr ::= 'if' expr 'then' expr 'else' expr
       | 'if' expr NL INDENT block DEDENT 'else' ( 'if' … | NL INDENT block DEDENT )
```

The condition is a `Bool`. On one line, `if c then a else b`. Across lines, each branch is an indented block and `else` is on a line of its own (or followed by another `if`). Every `if` has an `else`: both branches give a value of the same type (E0108 for a multi-line `if` without one).

```checkers
fn sign x -> s : x~Int, s~Int
    if x > 0
        1
    else if x < 0
        0 - 1
    else
        0
```

In each branch the condition is a fact: true in the first, false in the second ([Proofs](proofs.md#facts-in-scope)).

## `match`

```text
expr ::= 'match' expr NL INDENT { arm } DEDENT
arm  ::= pattern [ 'if' expr ] '->' ( expr NL | NL INDENT block DEDENT )
```

A `match` compares a value with the patterns of its arms, in order, and evaluates the first arm whose pattern matches and whose guard, if any, is true. Patterns and the cases a `match` must cover are in [Patterns and `match`](patterns.md).

## Lambdas

```text
expr ::= '\' apat { apat } '->' ( expr | NL INDENT block DEDENT )
```

A lambda is a function value. Its parameters are patterns, so `\(k, v) -> v` takes a pair apart. Its parameters' types come from where it is used (as an argument of `list.map`, say) or from its body.

```checkers
import std.list

check list.map (\x -> x * x) [1, 2, 3] == [1, 4, 9]
check list.map (\(k, v) -> k + v) [(1, 2), (3, 4)] == [3, 7]
```

A lambda may use the locals around it. Its body extends as far right as possible, so a lambda used as an argument is parenthesized (or follows `$`). A lambda whose body is an indented block is written outside brackets: `let f = \x ->` followed by the block.

## `try`

```text
expr ::= 'try' expr
```

`try e`, where `e` is a `Result a e2` or an `Option a`, gives the `Ok` or `Some` value; on `Err x` or `None` it returns that from the enclosing function at once. So the function's result type must be a `Result` with the same error type, or an `Option` (E0232). The value of `try` must be used where the enclosing block's value is the function's result: in a `let` of the function's body, not inside a lambda or another expression whose value is used elsewhere (E0230). `try` on anything else is E0231.

```checkers
fn parse_digit c -> r : c~U8, r~Result Nat String
    if '0' <= c and c <= '9' then Ok (c - '0') else Err "not a digit"

fn parse_two a b -> r : a~U8, b~U8, r~Result Nat String
    let x = try parse_digit a
    let y = try parse_digit b
    Ok (x * 10 + y)

check parse_two '4' '2' == Ok 42
check parse_two '4' 'x' == Err "not a digit"
```

## Field access and indexing

`r.f` reads the field `f` of a record `r` (E0207 if it has none). `a[i]` is element `i` of an array or of `Bytes`, and needs `i < len a` proven; lists are not indexed.

## Other expressions

- `len e` is the length of a `String` (in bytes), an `Array` or a `List`; `format e` renders any value as text ([Running programs](execution.md#format)). Both must be applied to their argument (E0214).
- `par (e1, e2, …)` evaluates the components in parallel ([Concurrency](concurrency.md#par)).
- `auto` and `admit` are allowed only in proofs (E0212, [Proofs](proofs.md)).
- `()` is the unit value; `(a, b)` a tuple; `[a, b]` a list.
