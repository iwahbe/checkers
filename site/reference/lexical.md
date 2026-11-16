# Lexical structure

A source file is UTF-8 text with the extension `.ck`. The compiler reads it as a sequence of tokens (names, keywords, literals, operators and punctuation), groups the tokens into logical lines, and turns indentation into the start and end of blocks.

## Comments

A comment starts with `#` outside a literal and runs to the end of the line. There are no block comments.

```checkers
# A comment on its own line.
fn double x -> y : x~Int, y~Int    # and one after code
    x + x
```

Comment lines directly above a declaration are its description, shown by the language server and in generated documentation ([Documentation comments](documentation.md)).

## Names

There are two kinds of name, told apart by their first letter:

| Kind | Form | Used for |
|---|---|---|
| `lname` | a lowercase letter or `_`, then letters, digits and `_` | values, functions, parameters, fields, modules, type variables |
| `Uname` | an uppercase letter, then letters, digits and `_` | types, constructors, constants |

`_` alone is not a name: it is the pattern that matches anything and binds nothing ([Patterns](patterns.md)), and is allowed only in patterns.

The spelling within each kind is a convention the compiler checks with warnings: `UpperCamelCase` for types and constructors (W001), `lower_snake_case` for functions, variables, fields and modules (W002), and `SCREAMING_SNAKE_CASE` for top-level constants (W003). A name starting with `_` is checked without it. Warnings never stop a program from compiling.

```checkers
type Small = n~Nat, n < 10

let LIMIT = 5

fn is_small n -> b : n~Nat, b~Bool
    n < LIMIT
```

## Keywords

These words are reserved and can't be used as names:

```text
module  import  as  export  abstract  transparent
fn  enum  record  type  let  class  instance
lemma  ensures  proof  have  auto  admit  check  forall
match  if  then  else  try  and  or  implies
decreasing  partial  ghost  own  comptime
when  using  par
```

Two more are keywords only in one place: `fork` right after `<-` and before `using`, and `join` right after `<-` and before a name and `=` ([Concurrency](concurrency.md)). Elsewhere they are ordinary names, so a function may be called `join`. `not`, `len` and `format` are ordinary functions of the prelude, not keywords.

A keyword where a name belongs is error E0122:

```checkers,compile_fail,E0122
fn first own n -> r : own~Nat, n~Nat, r~Nat
    n
```

## Literals

| Literal | Type | Examples |
|---|---|---|
| integer | `Int`, `Nat` or a fixed-width type, from what is expected; `Nat` if nothing decides | `42`, `0x2A`, `1_000_000` |
| byte, `'…'` | `U8` | `'a'`, `'\n'`, `'\''`, `'\x7f'` |
| character, `c'…'` | `Char` | `c'é'`, `c'\u{1F600}'` |
| string, `"…"` | `String` | `"hello"`, `"'"`, `"caf\u{e9}"` |
| bytes, `b"…"` | `Bytes` | `b"null"`, `b"\xff\x00"` |

**Integers** are written in decimal or, after `0x`, in hexadecimal. `_` may appear between digits and means nothing. A literal has no sign: `-1` is negation applied to `1`. There are no floating-point literals or types.

**Bytes** (`'a'`) hold one ASCII character or an escape, and are numbers: `'a' + 1 == 98`. **Characters** (`c'é'`) hold one Unicode scalar value. **Strings** and **bytes literals** end on the line they start; a newline inside one is written `\n`.

**Escapes:**

| Escape | Meaning | Allowed in |
|---|---|---|
| `\n` `\r` `\t` `\0` | newline, carriage return, tab, NUL | all |
| `\\` `\'` `\"` | a backslash, a single quote, a double quote | all |
| `\xNN` | the byte `NN` (two hex digits) | bytes and bytes literals; in strings and characters only up to `\x7f` |
| `\u{N…}` | the Unicode scalar value `N…` (one to six hex digits), as UTF-8 | strings, characters, bytes literals |

```checkers
check 'a' + 1 == 98
check "caf\u{e9}" == "café"
check b"\u{e9}" == b"\xc3\xa9"
check b"\xff"[0] == 255
```

## Operators and punctuation

```text
+  -  *  /  %  ++  ::  ==  !=  <  <=  >  >=  $  .
->  <-  =  ~  :  ,  |  \  (  )  [  ]  {  }
```

`and`, `or` and `implies` are operators written as keywords. Each operator's meaning and precedence is in [Expressions](expressions.md#operators).

The lexer takes the longest token it can, so `<-` is always one token: `x<-1` is a binding, not a comparison with `-1`. Write `x < -1`.

## Glued and spaced `.` and `[`

Whether `.` and `[` have a space before them changes what they mean:

| Written | Meaning |
|---|---|
| `p.x`, `list.map`, `xs[i]` (no space before) | field access, a qualified name, indexing |
| `f . g`, `f [x]` (a space before) | function composition, a list literal passed as an argument |

A glued `.` or `[` follows a name, a `)` or a `]`. It binds tighter than function application, so `Some p.x` is `Some (p.x)` and `f xs[0]` is `f (xs[0])`.

```checkers
import std.list

record Point
    x~Int
    y~Int

fn inc n -> m : n~Int, m~Int
    n + 1

check (inc . inc) 1 == 3
check list.length [1, 2, 3] == 3
check b"abc"[1] == 'b'
check (Point 1 2).y == 2
```

## Layout

The source is divided into **logical lines**. A newline ends a logical line, except when:

1. it is inside `( )`, `[ ]` or `{ }`;
2. the line's last token is `,` or a binary operator (`+ - * / % ++ :: == != < <= > >= and or implies $`, or `->` inside brackets); or
3. the next line's first token is a binary operator from that list, `.`, or `:`, and that line is indented further than the logical line's first line.

```checkers
fn total a b c -> s : a~Int, b~Int, c~Int,
                      s~Int
    a +
        b
        + c
```

A line that ends in `->`, `=` or `<-` outside brackets does not continue: it opens a block.

So a line starting with `-` at the indentation of the line before it starts a new logical line (a `match` arm `-1 -> …`), but one indented further continues it as a subtraction: the first line of an indented block can't start with a negation. Write `0 - 1`, or put the negation in parentheses, `(-1)`.

**Blocks.** When a logical line is followed by a more indented line, a block starts; it ends at the first line indented less. A block is part of the construct whose header line opened it: a function's body, the arms of a `match`, a branch of a multi-line `if`, a record's fields. A line may only return to an indentation that an enclosing block used (E0003).

```checkers,compile_fail,E0003
fn f x -> y : x~Int, y~Int
    if x > 0
        x
      else
        0
```

Indentation is spaces only: a tab in a line's leading white space is error E0001. Blank lines and lines holding only a comment don't affect layout.

**An unclosed bracket.** Inside a bracket newlines are ignored, so a missing `)` or `]` would swallow the declarations after it. A line that starts with a keyword that only ever begins a line (`fn`, `lemma`, `let`, `have`, `when`, `ensures`, `proof`, and others like them), and is indented no more than the line the bracket is on, closes the bracket instead, with error E0004 at the bracket. The declarations after it are then checked as usual.
