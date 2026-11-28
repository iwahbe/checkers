# Expressions

Checkers is expression-oriented: a function's body, an `if`, a `match` and a block each have a value. There are no statements apart from those inside blocks, no assignment and no loops: repetition is recursion ([Recursion and termination](termination.md)), and data is never changed in place.

## Blocks

A block is a sequence of lines at one indentation; its last line is its value.

```text
block ::= { stmt NL } expr NL
stmt  ::= 'let' pattern '=' ( expr | NL INDENT block DEDENT )
        | 'have' expr
        | 'have' lname '~' type
        | expr
        | when
```

**`let`** evaluates an expression and binds the pattern on its left to it, for the rest of the block. A `let` whose expression starts on the next line takes an indented block. The pattern must match every value of the type ([Patterns](patterns.md)): `let (q, r) = p` takes a tuple apart. `let` is also how a resource is threaded through operations on it: `let (line, f) = files.read_line f` ([Capabilities](effects.md#threading-a-resource)).

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

**`have`** adds a fact for the prover, or states a variable's type ([Proofs](proofs.md#have)); it has no effect when the program runs. **`when`** schedules a behaviour on cowns ([Concurrency](concurrency.md#when)).

## Names and literals

A lowercase name is a local (a parameter, a `let`, a pattern variable) or a function; an uppercase one is a constructor or a constant. `q.n` is the export `n` of the module imported as `q`. Literals are described in [Lexical structure](lexical.md#literals).

## Application

A function is applied by writing its arguments after it, separated by spaces: `f x y`. Application associates to the left, so `f x y` is `(f x) y`: every function takes its parameters one at a time, and applying it to fewer than all of them gives a function of the rest. Constructors are applied the same way (`Some x`, `Rect 2 3`).

Application binds tighter than every operator except a glued `.` and `[` ([Lexical structure](lexical.md#glued-and-spaced-and)): `f x + g y` is `(f x) + (g y)`, and `f p.x` is `f (p.x)`. An argument that is itself an application, an operator expression, an `if`, a `match`, a lambda or a `try` needs parentheses, or `$`. A `match`, a multi-line `if`, or a lambda whose body needs a block (a `let`), can't be in parentheses, since no block can start inside brackets ([Layout](lexical.md#layout)): it follows `$`, or is bound first with `let`.

`f -1` passes `-1` to `f`: a `-` glued to what follows, with a space before it, is a sign ([Lexical structure](lexical.md#signs)). `f - 1` and `f-1` subtract.

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

**Arithmetic** is on numbers, with the types and obligations given in [Types](types.md#numbers): `a - b` on `Nat`s needs `a >= b` (that section also shows a difference that may be negative), `/` and `%` need a non-zero divisor. On other types the arithmetic operators and comparisons work through classes ([Classes](classes.md#operators)); without an instance they are E0210.

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

A lambda may use the locals around it. Its body extends as far right as possible, and an argument must be an atom (a name, a literal, something in brackets), so a lambda passed to a function is parenthesized, `f (\x -> e)`, or follows `$`, `f $ \x -> e`. A lambda whose body is an indented block is written outside brackets, after `$` or `=`: `let f = \x ->` or `future.fork sched $ \_ ->`, followed by the block.

A lambda that uses a resource is a **one-shot closure**: it must be called exactly once ([Capabilities](effects.md#one-shot-closures)).

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

## Templates

A string glued to a function's name, `tag"text {e} text"`, is a **template**: the function, its *tag*, makes a formatter, which is given the text and the values in the holes in order, and then finishes. What a template builds, and which values its holes take, is up to the formatter (below, `page`).

A hole is written in one of four ways:

| Hole | Meaning |
|---|---|
| `{e}` | the value of the expression `e` |
| `{e \| o1, o2}` | `e`, with the options `o1` and `o2` |
| `{}` | a new parameter: the template is a function of its values, in order |
| `{\| o1, o2}` | a new parameter, with options |

The expressions in a hole are ordinary expressions in the template's scope, and errors in them are reported where they are written, inside the string. `|` separates the options only outside brackets, and the options are separated by commas, as in a list.

**Formatters.** A template is a series of calls of the classes `Template` and `Hole` of `std.string`. A template needs no import; a formatter's instances do, `import std.string (Template, Hole)`. The tag is applied to the number of bytes of text and the number of holes, and gives the formatter's first state; `Template.text` takes each piece of text, `Hole.hole` each hole's value and its options as a list, and `Template.finish` gives the result:

```text
fn tag n k -> p : n~Nat, k~Nat, p~Page
```

is a tag, and `tag"a{x}b{y | o}c"` means

```text
finish (text (hole (text (hole (text (tag 3 2) "a") x []) "b") y [o]) "c")
```

What a formatter accepts in its holes, and which options, is up to its instances of `Hole`, one for each type of value (or one for every type). A value of a type no instance takes is E0284 at the value. The tag is checked first: if it is unknown, or its result has no `Template` instance, that is the only error, at the tag, and the holes aren't checked:

```checkers
module page

import std.html
import std.list
import std.string (Template, Hole)

# HTML being built: its pieces, the last first.
record Page
    parts~List String

# What a hole may say about its value.
enum Mode
    Raw                        # the value as it is, not escaped

fn page n k -> p : n~Nat, k~Nat, p~Page
    Page []

instance Template Page
    type Result = String
    fn text p str
        Page (str :: p.parts)
    fn finish p
        string.concat (list.reverse p.parts)

# Strings only, escaped unless the hole says `Raw`.
instance Hole Page String
    type Options = Mode
    fn hole p x os
        Page ((if list.contains os Raw then x else html.escape x) :: p.parts)

check page"<p>{"a<b"}</p>{"<br>" | Raw}" == "<p>a&lt;b</p><br>"
check page"<li>{}</li>" "x" == "<li>x</li>"
```

```checkers,compile_fail,E0284
module page_count

import std.list
import std.string (Template, Hole)

record Page
    parts~List String

fn page n k -> p : n~Nat, k~Nat, p~Page
    Page []

instance Template Page
    type Result = String
    fn text p str
        Page (str :: p.parts)
    fn finish p
        string.concat (list.reverse p.parts)

instance Hole Page String
    fn hole p x os
        Page (x :: p.parts)

fn item count -> s : count~Nat, s~String
    page"<li>{count}</li>"
```

## Field access and indexing

`r.f` reads the field `f` of a record `r` (E0207 if it has none). `a[i]` is element `i` of an array or of `Bytes`, and needs `i < len a` proven; lists are not indexed.

## Other expressions

- `len e` is the length of a `String` (in bytes), an `Array` or a `List`. It must be applied to its argument (E0214). To show a value as text, see [Showing values](execution.md#showing-values).
- `par (e1, e2, …)` evaluates the components in parallel ([Concurrency](concurrency.md#par)).
- `auto` and `admit` are allowed only in proofs (E0212, [Proofs](proofs.md)).
- `()` is the unit value; `(a, b)` a tuple; `[a, b]` a list.
