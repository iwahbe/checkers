# Writing a parser

This guide builds a parser for CSV files, as [RFC 4180](https://www.rfc-editor.org/rfc/rfc4180) defines them, from bytes, one small function at a time. Nothing in it is checked at run time. The compiler proves that:

- every byte it reads, `src[i]`, is inside the input;
- it stops on every input: no loop can spin in place, and there is no fuel or step limit to run out;
- every error it reports points at a place in the input;
- it reads back every table its writer writes.

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
export transparent fn is_text b -> r : b~U8, r~Bool
    (b >= 0x20 and b <= 0x7E and b != '"' and b != ',') or b >= 0x80

# The end of the text that starts at `i`: the first byte that isn't text,
# or the end of the input. It may not move.
export transparent fn plain src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and is_text src[i] then plain src (i + 1) else i

# A byte that may appear in a quoted field as it is: text, a comma, or a
# line break.
export transparent fn is_quotable b -> r : b~U8, r~Bool
    is_text b or b == ',' or b == '\r' or b == '\n'

# Like `plain`, for what a quoted field holds as it is.
export transparent fn quotable src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and is_quotable src[i] then quotable src (i + 1) else i

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
export transparent fn inside src open i acc -> r : src~Bytes, open~Nat, i~Nat, open < i, i <= len src, acc~List Bytes,
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
export transparent fn quoted src i -> r : src~Bytes, i~Nat, i < len src, src[i] == '"',
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
export transparent fn field src i -> r : src~Bytes, i~Nat, i <= len src,
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
export transparent fn fields src i acc -> r : src~Bytes, i~Nat, i <= len src, acc~List Bytes,
                           r~Result (List Bytes, (j~Nat, i <= j, j <= len src)) (Error src)
    decreasing len src - i
    let (f, j) = try field src i
    if j < len src and src[j] == ','
        fields src (j + 1) (f :: acc)
    else
        Ok (list.reverse (f :: acc), j)

# The records from `i`, after `acc` (last first).
export transparent fn records src i acc -> r : src~Bytes, i~Nat, i <= len src, acc~List (List Bytes),
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
export transparent fn parse src -> r : src~Bytes, r~Result (List (List Bytes)) (Error src)
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

## Proving it reads back what it writes

A writer for the same format, and a proof that the parser reads back every table the writer writes: `parse (render rows) == Ok rows`. The writer quotes every field and doubles each `"` in it, as Python's `csv.writer` does with `quoting=csv.QUOTE_ALL`, and ends every record with CR LF.

Not every table can be written. A record with no fields has nothing to write, an empty table would be read back as one empty field, and a tab can't appear in a field even inside quotes. `writable_table` says which tables can be.

The proof unfolds the parser's functions, so it needs their bodies: that is why the modules above declare them `export transparent`. An `export fn` shows importers only its signature.

```checkers
module csv.render

import csv.scan (is_quotable, quotable)
import std.bytes

# ── Writing ──────────────────────────────────────────────────────────────────

# `f` from `i`, each `"` doubled. `quotable` finds the next `"`: in a field
# that can be written, it is the only byte `quotable` stops at.
export transparent fn escape f i -> r : f~Bytes, i~Nat, i <= len f, r~Bytes
    decreasing len f - i
    let k = quotable f i
    if k < len f then bytes.slice f i k ++ b"\"\"" ++ escape f (k + 1) else bytes.slice f i k

export transparent fn render_field f -> r : f~Bytes, r~Bytes
    b"\"" ++ escape f 0 ++ b"\""

export transparent fn render_row fs -> r : fs~List Bytes, r~Bytes
    match fs
        []        -> b""
        [f]       -> render_field f
        f :: rest -> render_field f ++ b"," ++ render_row rest

# The records, each ended by CR LF.
export transparent fn render rows -> r : rows~List (List Bytes), r~Bytes
    match rows
        []          -> b""
        row :: rest -> render_row row ++ b"\r\n" ++ render rest

check render [[b"a", b"x,\"y\""], [b""]] == b"\"a\",\"x,\"\"y\"\"\"\r\n\"\"\r\n"

# ── What can be written ──────────────────────────────────────────────────────

# Every byte of `f` from `i` may be in a quoted field: as it is, or doubled.
export transparent fn writable f i -> r : f~Bytes, i~Nat, i <= len f, r~Bool
    decreasing len f - i
    if i < len f then (is_quotable f[i] or f[i] == '"') and writable f (i + 1) else True

export transparent fn writable_row fs -> r : fs~List Bytes, r~Bool
    match fs
        []        -> True
        f :: rest -> writable f 0 and writable_row rest

# Records with at least one field each, of fields that can be written.
export transparent fn writable_table rows -> r : rows~List (List Bytes), r~Bool
    match rows
        []          -> True
        row :: rest -> row != [] and writable_row row and writable_table rest
```

The proof is the module below; its last lemma, `roundtrip`, is the result:

```text
lemma roundtrip rows : rows~List (List Bytes), rows != [], writable_table rows
    ensures parse (render rows) == Ok rows
```

Each lemma follows one parser function, and says what it does on rendered text with anything before it (`pre`) and anything after it (`post`) that can follow there. Induction follows the function's own recursion: on the list of fields or records (`match`), or on a position, with the same `decreasing` measure as the function. The `have` lines name the facts the prover needs: the standard library's facts about `slice` and `concat`, the lemma itself at the next step, and the steps of the parser's computation that the prover can't take alone.

```checkers
module csv.roundtrip

import csv (fields, records, parse)
import csv.scan (Error, is_quotable, quotable)
import csv.quoted (inside, quoted)
import csv.field (field)
import csv.render (escape, render_field, render_row, render, writable, writable_row, writable_table)
import std.bytes
import std.list

# A byte of the middle of three byte strings, and the byte after it.
lemma byte_in pre s post t : pre~Bytes, s~Bytes, post~Bytes, t~Nat, t < len s
    ensures (pre ++ s ++ post)[len pre + t] == s[t]

lemma byte_after pre s post t : pre~Bytes, s~Bytes, post~Bytes, t~Nat, t < len post
    ensures (pre ++ s ++ post)[len pre + len s + t] == post[t]

# What follows a closing quote isn't another quote.
lemma after_quote pre s post : pre~Bytes, s~Bytes, post~Bytes, len post == 0 or post[0] != '"'
    let src = pre ++ s ++ b"\"" ++ post
    let q = len pre + len s
    ensures q + 1 == len src or src[q + 1] != '"'
    proof
        if len post == 0 then auto else have byte_after (pre ++ s) b"\"" post 0

# Scanning a slice of `f`, placed in a larger input, stops where scanning
# `f` stops.
lemma scan_slice pre f i k post x : pre~Bytes, f~Bytes, i~Nat, k~Nat, x~Nat, i <= x, x <= k, k <= len f,
                                    quotable f x == k, post~Bytes, len post > 0, not (is_quotable post[0])
    let src = pre ++ bytes.slice f i k ++ post
    ensures quotable src (len pre + (x - i)) == len pre + (k - i)
    proof
        decreasing k - x
        if x < k
            let p = len pre + (x - i)
            have bytes.slice_at f i k (x - i)
            have byte_in pre (bytes.slice f i k) post (x - i)
            have src[p] == f[x]
            have quotable f x == quotable f (x + 1)
            have is_quotable f[x]
            have quotable src p == quotable src (p + 1)
            have scan_slice pre f i k post (x + 1)
        else
            have byte_after pre (bytes.slice f i k) post 0
            have src[len pre + (k - i)] == post[0]
            auto

# In a field that can be written, `quotable` stops at a `"` or the end.
lemma writable_stop f i : f~Bytes, i~Nat, i <= len f, writable f i
    let k = quotable f i
    ensures (k == len f or f[k] == '"') and writable f k
    proof
        if i < len f and is_quotable f[i] then have writable_stop f (i + 1) else auto

lemma concat_append xs ys : xs~List Bytes, ys~List Bytes
    ensures bytes.concat (xs ++ ys) == bytes.concat xs ++ bytes.concat ys
    proof
        match xs
            []        -> have bytes.concat_nil
            x :: rest ->
                have bytes.concat_cons x (rest ++ ys)
                have bytes.concat_cons x rest
                have concat_append rest ys

# The pieces `inside` collects, last first, joined.
lemma concat_snoc acc x : acc~List Bytes, x~Bytes
    ensures bytes.concat (list.reverse (x :: acc)) == bytes.concat (list.reverse acc) ++ x
    proof
        have list.reverse_cons_append acc x []
        have list.append_nil (list.reverse (x :: acc))
        have concat_append (list.reverse acc) [x]
        have bytes.concat_cons x []
        have bytes.concat_nil

# What `quoted` makes of `inside`'s result.
fn joined src r -> o : src~ghost Bytes, r~Result (List Bytes, Nat) (Error src), o~Option (Bytes, Nat)
    match r
        Ok (parts, j) -> Some (bytes.concat (list.reverse parts), j)
        Err _         -> None

# One step of `inside`, past a doubled quote.
lemma inside_step src open p acc q : src~Bytes, open~Nat, p~Nat, open < p, p <= len src, acc~List Bytes, q~Nat,
                                     quotable src p == q, q + 1 < len src, src[q] == '"', src[q + 1] == '"'
    ensures joined src (inside src open p acc) == joined src (inside src open (q + 2) (b"\"" :: bytes.slice src p q :: acc))
    proof
        match inside src open (q + 2) (b"\"" :: bytes.slice src p q :: acc)
            Ok (parts, j) -> have inside src open p acc == Ok (parts, j)
            Err e         -> have inside src open p acc == Err e

# The last step of `inside`, at the closing quote.
lemma inside_last src open p acc q : src~Bytes, open~Nat, p~Nat, open < p, p <= len src, acc~List Bytes, q~Nat,
                                     quotable src p == q, q < len src, src[q] == '"',
                                     q + 1 == len src or src[q + 1] != '"'
    ensures joined src (inside src open p acc)
         == Some (bytes.concat (list.reverse (bytes.slice src p q :: acc)), q + 1)

# `inside` reads an escaped field back, up to its closing quote.
lemma inside_escape src pre f i post open acc
    : pre~Bytes, f~Bytes, i~Nat, i <= len f, writable f i, post~Bytes, len post == 0 or post[0] != '"',
      src~Bytes, src == pre ++ escape f i ++ b"\"" ++ post, open~Nat, open < len pre, acc~List Bytes
    ensures joined src (inside src open (len pre) acc)
         == Some (bytes.concat (list.reverse acc) ++ bytes.slice f i (len f), len pre + len (escape f i) + 1)
    proof
        decreasing len f - i
        let k = quotable f i
        let s = bytes.slice f i k
        have writable_stop f i
        if k < len f
            let rest = b"\"\"" ++ escape f (k + 1) ++ b"\"" ++ post
            have src == pre ++ s ++ rest
            have scan_slice pre f i k rest i
            have bytes.slice_append pre s rest
            let q = len pre + (k - i)
            have len s == k - i
            have bytes.slice src (len pre) (len pre + len s) == s
            have quotable src (len pre) == q
            have src[q] == '"' and q + 1 < len src and src[q + 1] == '"'
            have bytes.slice src (len pre) q == s
            have inside_step src open (len pre) acc q
            have len (escape f i) == (k - i) + 2 + len (escape f (k + 1))
            let pre2 = pre ++ s ++ b"\"\""
            have src == pre2 ++ escape f (k + 1) ++ b"\"" ++ post
            have inside_escape src pre2 f (k + 1) post open (b"\"" :: s :: acc)
            have len pre2 == q + 2
            have len (escape f i) == (k - i) + 2 + len (escape f (k + 1))
            have concat_snoc acc s
            have concat_snoc (s :: acc) b"\""
            have bytes.slice_at f k (k + 1) 0
            have bytes.slice f k (k + 1) == b"\""
            have bytes.slice_join f k (k + 1) (len f)
            have bytes.slice_join f i k (len f)
            have s ++ b"\"" ++ bytes.slice f (k + 1) (len f) == bytes.slice f i (len f)
            let acc2 = b"\"" :: s :: acc
            have joined src (inside src open (len pre) acc) == joined src (inside src open (len pre2) acc2)
            have joined src (inside src open (len pre2) acc2)
              == Some (bytes.concat (list.reverse acc) ++ s ++ b"\"" ++ bytes.slice f (k + 1) (len f),
                       len pre2 + len (escape f (k + 1)) + 1)
            auto
        else
            let rest = b"\"" ++ post
            have src == pre ++ s ++ rest
            have scan_slice pre f i k rest i
            have bytes.slice_append pre s rest
            let q = len pre + (k - i)
            have len s == k - i
            have bytes.slice src (len pre) (len pre + len s) == s
            have quotable src (len pre) == q
            have byte_after pre s rest 0
            have src[q] == '"'
            have after_quote pre s post
            have bytes.slice src (len pre) q == s
            have inside_last src open (len pre) acc q
            have concat_snoc acc s
            auto

# `field` reads a rendered field back.
lemma field_render pre f post : pre~Bytes, f~Bytes, writable f 0, post~Bytes, len post == 0 or post[0] != '"'
    let src = pre ++ render_field f ++ post
    ensures field src (len pre) == Ok (f, len pre + len (render_field f))
    proof
        let pre2 = pre ++ b"\""
        have src[len pre] == '"'
        have src == pre2 ++ escape f 0 ++ b"\"" ++ post
        have inside_escape src pre2 f 0 post (len pre) []
        have bytes.slice_append b"" f b""
        have bytes.concat_nil
        let e = len pre + len (render_field f)
        have b"" ++ f ++ b"" == f
        have bytes.slice f 0 (len f) == f
        have bytes.concat (list.reverse []) == b""
        have e == len pre2 + len (escape f 0) + 1
        have joined src (inside src (len pre) (len pre + 1) []) == Some (f, e)
        match inside src (len pre) (len pre + 1) []
            Ok (parts, j) ->
                have joined src (Ok (parts, j)) == Some (bytes.concat (list.reverse parts), j)
                have bytes.concat (list.reverse parts) == f and j == e
                have quoted src (len pre) == Ok (f, e)
                auto
            Err _         -> auto

# `fields` reads a rendered record back, up to its CR LF.
lemma fields_render pre fs post acc : pre~Bytes, fs~List Bytes, fs != [], writable_row fs, post~Bytes,
                                      len post == 0 or post[0] == '\r', acc~List Bytes
    let src = pre ++ render_row fs ++ post
    ensures fields src (len pre) acc == Ok (list.reverse acc ++ fs, len pre + len (render_row fs))
    proof
        match fs
            [f]       ->
                let e = len pre + len (render_row fs)
                have render_row fs == render_field f
                have field_render pre f post
                have field src (len pre) == Ok (f, e)
                have not (e < len src and src[e] == ',')
                have list.reverse_cons_append acc f []
                have list.append_nil (list.reverse (f :: acc))
                have list.reverse (f :: acc) == list.reverse acc ++ fs
                auto
            f :: rest ->
                have rest != []
                have render_row fs == render_field f ++ b"," ++ render_row rest
                let post2 = b"," ++ render_row rest ++ post
                have src == pre ++ render_field f ++ post2
                have field_render pre f post2
                let e = len pre + len (render_field f)
                have field src (len pre) == Ok (f, e)
                have e < len src and src[e] == ','
                have fields src (len pre) acc == fields src (e + 1) (f :: acc)
                let pre2 = pre ++ render_field f ++ b","
                have len pre2 == e + 1
                have src == pre2 ++ render_row rest ++ post
                have fields_render pre2 rest post (f :: acc)
                have list.reverse_cons_append acc f rest
                auto

# `records` reads the rendered records back, to the end of the input.
lemma records_render pre rows acc : pre~Bytes, rows~List (List Bytes), rows != [], writable_table rows,
                                           acc~List (List Bytes)
    let src = pre ++ render rows
    ensures records src (len pre) acc == Ok (list.reverse acc ++ rows)
    proof
        match rows
            row :: rest ->
                let post = b"\r\n" ++ render rest
                have src == pre ++ render_row row ++ post
                have fields_render pre row post []
                let e = len pre + len (render_row row)
                have list.reverse [] ++ row == row
                have fields src (len pre) [] == Ok (row, e)
                have src[e] == '\r' and src[e + 1] == '\n'
                match rest
                    []     ->
                        have e + 2 == len src
                        have records src (len pre) acc == Ok (list.reverse (row :: acc))
                        have list.reverse_cons_append acc row []
                        have list.append_nil (list.reverse (row :: acc))
                        auto
                    _ :: _ ->
                        have len (render rest) > 0
                        have records src (len pre) acc == records src (e + 2) (row :: acc)
                        let pre2 = pre ++ render_row row ++ b"\r\n"
                        have len pre2 == e + 2
                        have src == pre2 ++ render rest
                        have records_render pre2 rest (row :: acc)
                        have list.reverse_cons_append acc row rest
                        auto

# The parser reads back every table the writer writes.
export lemma roundtrip rows : rows~List (List Bytes), rows != [], writable_table rows
    ensures parse (render rows) == Ok rows
    proof
        have records_render b"" rows []
```

## The pattern

- A **scanner** moves over what it can and may not move: its result is `j` with `i <= j`. A loop around a scanner must move by itself, as `fields` does past each comma.
- A **token** parser consumes at least one byte when it succeeds: `i < j`. A loop around a token parser ends.
- Every result also says `j <= len src`, so the next read can be guarded by `j < len src` and the next error built at `j`.
- `decreasing len src - i` is the measure for every loop: each recursive call is at a position the compiler can see is further on.
- `try` passes errors up; what a callee promised about its result is known after it.
- A proof about a parser follows the parser: one lemma per function, about rendered text between any `pre` and `post`, by induction on the function's own measure.
