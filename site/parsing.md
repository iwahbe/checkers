# Writing a parser

This guide builds a parser for CSV files, as [RFC 4180](https://www.rfc-editor.org/rfc/rfc4180) defines them, from bytes, one small function at a time. Nothing in it is checked at run time. The compiler proves that:

- every byte it reads, `src[i]`, is inside the input;
- it stops on every input: no loop can spin in place, and there is no fuel or step limit to run out;
- every error it reports points at a place in the input.

The same pattern works for any format read from left to right. A position into the input goes forward, each function says how far it may have moved, and those promises are what the compiler uses to see that the loops end.

## The format

RFC 4180's grammar, from its section 2:

```text
file        = [header CRLF] record *(CRLF record) [CRLF]
record      = field *(COMMA field)
field       = (escaped / non-escaped)
escaped     = DQUOTE *(TEXTDATA / COMMA / CR / LF / 2DQUOTE) DQUOTE
non-escaped = *TEXTDATA
TEXTDATA    = %x20-21 / %x23-2B / %x2D-7E
```

A record is a line of fields separated by commas. A field is either plain text or enclosed in double quotes; a quoted field may hold commas and line breaks, and writes a `"` inside it as `""`. Lines end with CR LF.

The parser follows the grammar. Where the RFC leaves a choice open, it does what Python's [`csv`](https://docs.python.org/3/library/csv.html) module does. Its contract:

| Input | Result |
|---|---|
| `a,b` CR LF `c,d` | two records, `[a, b]` and `[c, d]` |
| `a` CR LF | one record: the last line break is optional, and ends the last record |
| `"x,""y"""` | one field, `x,"y"` |
| empty input, or CR LF alone | one record with one empty field, as the grammar says |
| `a` CR LF CR LF | two records, `[a]` and one with an empty field |
| records with different numbers of fields | allowed (the RFC says they *should* have the same number) |
| bytes from 128 up | allowed in fields, as text in another character set |
| a line break that is LF alone | an error: lines end with CR LF |
| `"` in a plain field, or text after a closing quote | an error |
| a quoted field with no closing quote | an error, at its opening quote |
| a tab, or another control byte outside a quoted field | an error |

Fields are returned as `Bytes`, without decoding them.

## Errors

An error says what went wrong and where. Its `src` parameter exists only in the type (`ghost`), so that `pos <= len src` can be part of it: an error can't point past the end of the input it came from.

```checkers
module csv.scan

# What went wrong.
export enum Problem
    # A byte that can't come here.
    UnexpectedByte b : b~U8
    # The input ended where it can't.
    UnexpectedEnd
    # A quoted field with no closing quote; the error points at the opening one.
    Unclosed

# A problem at a position in `src`.
export record Error src : src~ghost Bytes
    pos~Nat, pos <= len src
    problem~Problem

# A byte that may appear in a field as it is: printable ASCII other than
# `"` and `,`, or any byte from 128 up.
export fn is_text b -> r : b~U8, r~Bool
    (b >= 0x20 and b <= 0x7E and b != '"' and b != ',') or b >= 0x80

# The end of the text that starts at `i`: the first byte that isn't text,
# or the end of the input. It may not move.
export fn plain src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and is_text src[i] then plain src (i + 1) else i

# Like `plain`, but also going over what a quoted field holds as it is:
# commas and line breaks.
export fn quotable src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and (is_text src[i] or src[i] == ',' or src[i] == '\r' or src[i] == '\n')
        quotable src (i + 1)
    else
        i

check plain b"ab,c" 0 == 2
check plain b",c" 0 == 0
```

`plain` is a **scanner**: it moves forward over the text at `i`, and may not move at all (`plain b",c" 0` is `0`). Its signature says so: `i <= j`. It also promises `j <= len src`, so its caller can read `src[j]` after checking `j < len src`.

`plain` calls itself with `i + 1`, and `decreasing len src - i` names the measure that gets smaller with each call: the number of bytes left. The compiler proves the measure is a `Nat` (it follows from `i < len src` in the branch) and that it decreases. It would guess this measure without the `decreasing` line ([Recursion and termination](reference/termination.md#guessed-measures)); writing it puts the argument where a reader sees it.

## Tokens: parsers that always move

A quoted field is a **token**: when it is recognized, at least its two quotes are consumed. Its result says so with `i < j`, and that promise is what lets a loop of tokens end.

```checkers
module csv.quoted

import csv.scan (Error, Problem, quotable)
import std.bytes
import std.list

# The quoted field whose opening quote is at `open`, read from `i`: its
# pieces, last first, after `acc`, and the position after its closing quote.
fn inside src open i acc -> r : src~Bytes, open~Nat, i~Nat, open < i, i <= len src, acc~List Bytes,
                                r~Result (List Bytes, (j~Nat, i < j, j <= len src)) (Error src)
    decreasing len src - i
    let k = quotable src i
    if k == len src
        Err (Error open Unclosed)
    else if src[k] != '"'
        Err (Error k (UnexpectedByte src[k]))
    else if k + 1 < len src and src[k + 1] == '"'
        let (parts, j) = try inside src open (k + 2) (b"\"" :: bytes.slice src i k :: acc)
        Ok (parts, j)
    else
        Ok (bytes.slice src i k :: acc, k + 1)

# The quoted field at `i`, which starts with `"`: its text, with each `""`
# read as `"`, and the position after its closing quote.
export fn quoted src i -> r : src~Bytes, i~Nat, i < len src, src[i] == '"',
                              r~Result (Bytes, (j~Nat, i < j, j <= len src)) (Error src)
    let (parts, j) = try inside src i (i + 1) []
    Ok (bytes.concat (list.reverse parts), j)

check quoted b"\"a\"\"b\",c" 0 == Ok (b"a\"b", 6)
check quoted b"\"ab" 0 == Err (Error 0 Unclosed)
```

`try` takes the `Ok` value of a `Result` apart, or returns its `Err` from the function. After `let (parts, j) = try inside …`, the compiler knows what `inside` promised about `j`, that `k + 2 < j`, and from that, what `inside` itself must promise, `i < j`.

`inside` loops once for each `""` in the field. Its recursive call is at `k + 2`, past the scanner's end and the two quotes, and the measure `len src - i` decreases because `quotable` moved forward or stayed put (`i <= k`), never back.

## Composing

A field is either quoted or plain. A plain field may be empty, so `field` promises only `i <= j`:

```checkers
module csv.field

import csv.scan (Error, plain)
import csv.quoted (quoted)
import std.bytes

# The field at `i` and the position after it.
export fn field src i -> r : src~Bytes, i~Nat, i <= len src,
                             r~Result (Bytes, (j~Nat, i <= j, j <= len src)) (Error src)
    if i < len src and src[i] == '"'
        let (f, j) = try quoted src i
        Ok (f, j)
    else
        let j = plain src i
        Ok (bytes.slice src i j, j)

check field b"ab,c" 0 == Ok (b"ab", 2)
check field b",c" 0 == Ok (b"", 0)
```

The `if` passes on what it learned: in the first branch `i < len src and src[i] == '"'` holds, which is exactly what `quoted` requires. Calling `quoted` anywhere else is an error that says which requirement isn't known to hold.

A record is fields separated by commas. `field` may not move, so a loop that called it again at the same place would never end. Here each next call is after a comma, at `j + 1`, so the measure decreases even when the field was empty:

```checkers
module csv

import csv.scan (Error, Problem)
import csv.field (field)
import std.list

# The fields of the record at `i`, after `acc` (last first), and where the
# record ends.
fn fields src i acc -> r : src~Bytes, i~Nat, i <= len src, acc~List Bytes,
                           r~Result (List Bytes, (j~Nat, i <= j, j <= len src)) (Error src)
    decreasing len src - i
    let (f, j) = try field src i
    if j < len src and src[j] == ','
        fields src (j + 1) (f :: acc)
    else
        Ok (list.reverse (f :: acc), j)

# The records from `i`, after `acc` (last first).
fn records src i acc -> r : src~Bytes, i~Nat, i <= len src, acc~List (List Bytes),
                            r~Result (List (List Bytes)) (Error src)
    decreasing len src - i
    let (row, j) = try fields src i []
    let rows = row :: acc
    if j == len src
        Ok (list.reverse rows)
    else if src[j] != '\r'
        Err (Error j (UnexpectedByte src[j]))
    else if j + 1 == len src
        Err (Error (j + 1) UnexpectedEnd)
    else if src[j + 1] != '\n'
        Err (Error (j + 1) (UnexpectedByte src[j + 1]))
    else if j + 2 == len src
        Ok (list.reverse rows)
    else
        records src (j + 2) rows

# The records of a CSV file (RFC 4180), each a list of its fields.
export fn parse src -> r : src~Bytes, r~Result (List (List Bytes)) (Error src)
    records src 0 []
```

`records` repeats on the same argument: every record after the first follows a CR LF, so the next call is at `j + 2` and the input left shrinks by at least two bytes. The loop needs no limit on how many records it reads.

Each `Err` in `records` is built where the compiler can see its position is at most `len src`: `j` because `fields` promised `j <= len src`, and `j + 1` because the branch it is in has ruled out `j + 1 > len src`. Writing `Error (j + 2) UnexpectedEnd` in the third branch instead fails to check, with the input that shows why:

```text
error[E0450]: cannot prove `pos <= len src`, required to build `Error`
   |
   |         Err (Error (j + 2) UnexpectedEnd)
   |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ `Error` requires `pos <= len src`
   = note: counterexample: src = b"\r", i = 0
```

A CR at the end of the input: `j` is 0, and `j + 2` is past the end.

## What it does

`check` lines are run by the compiler; a false one is an error. These show the contract above:

```checkers
import csv (parse)
import csv.scan (Error, Problem)

# Two records; the last line break is optional.
check parse b"12,34\r\n56,78" == Ok [[b"12", b"34"], [b"56", b"78"]]
check parse b"12,34\r\n" == Ok [[b"12", b"34"]]

# Quoted fields hold commas, line breaks and quotes.
check parse b"\"a,b\",\"c\r\nd\",\"say \"\"hi\"\"\"" == Ok [[b"a,b", b"c\r\nd", b"say \"hi\""]]

# Empty input, and an empty line, are one empty field.
check parse b"" == Ok [[b""]]
check parse b"\r\n" == Ok [[b""]]
check parse b"a\r\n\r\nb" == Ok [[b"a"], [b""], [b"b"]]

# Empty fields, and records of different lengths.
check parse b",\r\na" == Ok [[b"", b""], [b"a"]]

# Bytes from 128 up are text.
check parse b"caf\xc3\xa9" == Ok [[b"caf\xc3\xa9"]]

# A line break must be CR LF.
check parse b"12,34\n" == Err (Error 5 (UnexpectedByte '\n'))
check parse b"12,34\r" == Err (Error 6 UnexpectedEnd)

# A quote in a plain field, text after a closing quote, a quote not closed.
check parse b"a\"b" == Err (Error 1 (UnexpectedByte '"'))
check parse b"\"a\"b" == Err (Error 3 (UnexpectedByte 'b'))
check parse b"x,\"ab" == Err (Error 2 Unclosed)

# A tab isn't text.
check parse b"a\tb" == Err (Error 1 (UnexpectedByte '\t'))
```

## Reading numbers from fields

A field's bytes can be parsed again. A decimal number is one or more digits; `digits` is a token, so it promises `i < j`, and `more`, which reads the digits after the first, is a scanner that may not move:

```checkers
module csv.number

fn is_digit b -> r : b~U8, r~Bool
    b >= '0' and b <= '9'

# The digits from `i`, read after `n`, and where they end.
fn more src i n -> r : src~Bytes, i~Nat, i <= len src, n~Nat, r~(Nat, (j~Nat, i <= j, j <= len src))
    decreasing len src - i
    if i < len src and is_digit src[i] then more src (i + 1) (n * 10 + (src[i] - '0')) else (n, i)

# One or more digits at `i`: their value, and where they end.
fn digits src i -> r : src~Bytes, i~Nat, r~Option (Nat, (j~Nat, i < j, j <= len src))
    if i < len src and is_digit src[i]
        let (n, j) = more src (i + 1) (src[i] - '0')
        Some (n, j)
    else
        None

# The number a field holds: digits and nothing else.
export fn number f -> r : f~Bytes, r~Option Nat
    match digits f 0
        Some (n, j) -> if j == len f then Some n else None
        None        -> None

check number b"1234" == Some 1234
check number b"" == None
check number b"12a" == None
check number b"-1" == None
```

`src[i] - '0'` is subtraction of `Nat`s, which needs `src[i] >= '0'`: the compiler finds it in `is_digit src[i]`, whose body it can see because it is in the same module.

## The pattern

- A **scanner** moves over what it can and may not move: its result is `j` with `i <= j`. A loop around a scanner must move by itself, as `fields` does past each comma.
- A **token** parser consumes at least one byte when it succeeds: `i < j`. A loop around a token parser ends.
- Every result also says `j <= len src`, so the next read can be guarded by `j < len src` and the next error built at `j`.
- `decreasing len src - i` is the measure for every loop: each recursive call is at a position the compiler can see is further on.
- `try` passes errors up; what a callee promised about its result is known after it.
