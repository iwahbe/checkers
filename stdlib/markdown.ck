# markdown.ck — Markdown to a syntax tree and to HTML: CommonMark 0.31.2
# (https://spec.commonmark.org/0.31.2/), every example of its spec (D148,
# D151).
#
# A port of commonmark.js (https://github.com/commonmark/commonmark.js), the
# reference implementation by the spec's author, restated without mutation:
# lines become blocks first, then each paragraph's and heading's text becomes
# inlines. Its notice:
#
#     Copyright (c) 2014, John MacFarlane
#
#     All rights reserved.
#
#     Redistribution and use in source and binary forms, with or without
#     modification, are permitted provided that the following conditions are
#     met:
#
#         * Redistributions of source code must retain the above copyright
#           notice, this list of conditions and the following disclaimer.
#
#         * Redistributions in binary form must reproduce the above
#           copyright notice, this list of conditions and the following
#           disclaimer in the documentation and/or other materials provided
#           with the distribution.
#
#     THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
#     "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
#     LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
#     A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
#     OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
#     SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
#     LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
#     DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
#     THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
#     (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
#     OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# Links' destinations are percent-encoded as commonmark.js's dependency
# mdurl does (`encode`, MIT License, Copyright (c) 2015 Vitaly Puzrin, Alex
# Kocharin), and numeric character references decoded as its dependency
# entities does (`replaceCodePoint`, after HTML's table for the C1 controls).
module std.markdown

import std.array
import std.bytes
import std.char
import std.html
import std.list
import std.string
import std.utf8

# ── The syntax tree ──────────────────────────────────────────────────────────

# Where something is in the parsed text: its bytes from `start` up to (not
# including) `stop`.
export record Span
    start~Nat
    stop~Nat

# Where a link or an image goes, and its title, if it has one.
export record Target
    url~String
    title~Option String

# One item of a list: its blocks.
export record Item
    blocks~List Block
    span~Span

# A link reference definition, `[label]: url "title"`. `label` is as written,
# without its brackets.
export record Definition
    label~String
    target~Target
    span~Span

# Bracketed text that could have been a reference to a definition, matched
# none, and wasn't resolved (`parse_with`): `[label]`, `[text][label]` or
# `[label][]`. `label` is as written, without its brackets.
export record Reference
    label~String
    span~Span

# A block: a paragraph, a heading (`level` 1 to 6), a thematic break, a
# block quote, a list (`tight` when its items' paragraphs aren't separated
# by blank lines; a numbered list starts at `start`), code (its info string,
# its text, and the span of each line of the text), or raw HTML.
export enum Block
    Paragraph inlines span          : inlines~List Inline, span~Span
    Heading level inlines span      : level~Nat, inlines~List Inline, span~Span
    ThematicBreak span              : span~Span
    Quote blocks span               : blocks~List Block, span~Span
    Bullets tight items span        : tight~Bool, items~List Item, span~Span
    Numbered start tight items span : start~Nat, tight~Bool, items~List Item, span~Span
    Code info text lines span       : info~String, text~String, lines~List Span, span~Span
    Html text span                  : text~String, span~Span

# Inline content: text (character references and backslash escapes already
# replaced), a code span, emphasis, strong emphasis, a link or an image
# (`ref`: the label of the definition or resolved reference it came from, as
# written), raw HTML, and line breaks: soft (a line ending) and hard.
export enum Inline
    Text text span                : text~String, span~Span
    CodeSpan text span            : text~String, span~Span
    Emph inlines span             : inlines~List Inline, span~Span
    Strong inlines span           : inlines~List Inline, span~Span
    Link target inlines ref span  : target~Target, inlines~List Inline, ref~Option String, span~Span
    Image target inlines ref span : target~Target, inlines~List Inline, ref~Option String, span~Span
    RawHtml text span             : text~String, span~Span
    SoftBreak span                : span~Span
    HardBreak span                : span~Span

# A parsed document: its blocks, its link reference definitions (in order;
# when two have the same label, the first is the one used), and the
# references that matched no definition.
export record Document
    blocks~List Block
    definitions~List Definition
    unresolved~List Reference

# ── Bytes ────────────────────────────────────────────────────────────────────

# The byte at `i`, or 256 past the end.
fn at b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b then b[i] else 256

# The bytes from `i` to `j`, as far as `b` has them.
fn part b i j -> r : b~Bytes, i~Nat, j~Nat, r~Bytes
    let k = if j <= len b then j else len b
    if i <= k then bytes.slice b i k else b""

fn sub a b -> r : a~Nat, b~Nat, r~Nat
    if a >= b then a - b else 0

fn min a b -> r : a~Nat, b~Nat, r~Nat
    if a <= b then a else b

fn max a b -> r : a~Nat, b~Nat, r~Nat
    if a >= b then a else b

fn text_of b -> r : b~Bytes, r~String
    match string.from_utf8 b
        Some s -> s
        None   -> ""

fn joined parts -> r : parts~List Bytes, r~Bytes
    bytes.concat (list.reverse parts)

fn is_space_or_tab c : c~Nat
    c == 32 or c == 9

# A space, a tab, a line ending, a form feed or a vertical tab.
fn is_ascii_space c : c~Nat
    c == 32 or c == 9 or c == 10 or c == 11 or c == 12 or c == 13

fn is_digit c : c~Nat
    c >= 48 and c <= 57

fn is_hex c : c~Nat
    is_digit c or (c >= 97 and c <= 102) or (c >= 65 and c <= 70)

fn is_letter c : c~Nat
    (c >= 97 and c <= 122) or (c >= 65 and c <= 90)

fn is_alnum c : c~Nat
    is_letter c or is_digit c

fn lower c -> r : c~Nat, r~Nat
    if c >= 65 and c <= 90 then c + 32 else c

# ASCII punctuation: what a backslash escapes.
fn is_escapable c : c~Nat
    (c >= 33 and c <= 47) or (c >= 58 and c <= 64) or (c >= 91 and c <= 96) or (c >= 123 and c <= 126)

# Where the run of bytes satisfying `p` from `i` ends.
fn skip p b i -> r : p~(Nat -> Bool), b~Bytes, i~Nat, r~Nat, i <= r, (i <= len b implies r <= len b),
                     ((i < len b and p b[i]) implies r > i)
    if i < len b and p b[i] then skip p b (i + 1) else i

# Where the run of `c` from `i` ends.
fn skip_byte c b i -> r : c~Nat, b~Bytes, i~Nat, r~Nat, i <= r, (i <= len b implies r <= len b),
                          ((i < len b and b[i] == c) implies r > i)
    if i < len b and b[i] == c then skip_byte c b (i + 1) else i

# The first `i` from `from` at which `word` occurs, if any.
fn find b word from -> r : b~Bytes, word~Bytes, from~Nat, r~Option Nat
    if from + len word > len b
        None
    else if bytes.matches_at b from word
        Some from
    else
        find b word (from + 1)

# Whether `b` has `word` at `i`, ignoring ASCII case (`word` is lower case).
fn matches_lower b i word -> r : b~Bytes, i~Nat, word~Bytes, r~Bool
    if i + len word > len b then False else same_lower b i word 0

fn same_lower b i word k -> r : b~Bytes, i~Nat, word~Bytes, k~Nat, r~Bool
    if k < len word
        lower (at b (i + k)) == word[k] and same_lower b i word (k + 1)
    else
        True

# Without spaces and tabs at either end.
fn trim b -> r : b~Bytes, r~Bytes
    let i = skip is_space_or_tab b 0
    part b i (trim_end is_space_or_tab b (len b) i)

# Where the run of bytes satisfying `p` that ends at `j` (and not before
# `lo`) starts.
fn trim_end p b j lo -> r : p~(Nat -> Bool), b~Bytes, j~Nat, lo~Nat, r~Nat
    if j > lo and p (at b (j - 1)) then trim_end p b (j - 1) lo else j

# `b` with each NUL as U+FFFD, as the spec asks for security.
fn clean b -> r : b~Bytes, r~Bytes
    match find b b"\x00" 0
        None   -> b
        Some _ -> joined (clean_from b 0 0 [])

fn clean_from b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    decreasing sub (len b) i
    if i < len b
        if b[i] == 0
            clean_from b (i + 1) (i + 1) (b"\xEF\xBF\xBD" :: part b start i :: acc)
        else
            clean_from b start (i + 1) acc
    else
        part b start i :: acc

# The bytes of `n` in decimal.
fn decimal n -> r : n~Nat, r~Bytes
    string.bytes (format n)

# ── Characters ───────────────────────────────────────────────────────────────

# The character whose UTF-8 encoding starts at `i`; U+FFFD for a byte that
# doesn't start one, and `None` at the end.
fn char_at b i -> r : b~Bytes, i~Nat, r~Option Char
    if i < len b
        match utf8.decode_at b i
            Some p -> Some p.value
            None   -> Some c'\u{FFFD}'
    else
        None

# Where the character before `i` starts.
fn char_before b i -> r : b~Bytes, i~Nat, r~Nat
    if i > 0 and at b (i - 1) >= 0x80 and at b (i - 1) < 0xC0 and i > 1
        if at b (i - 2) >= 0xC0 or at b (i - 2) < 0x80 or i < 3
            i - 2
        else if at b (i - 3) >= 0xC0 or at b (i - 3) < 0x80 or i < 4
            i - 3
        else
            i - 4
    else
        sub i 1

# Unicode white space as CommonMark has it: a tab, a line feed, a form feed,
# a carriage return, or a space separator (general category Zs).
fn is_unicode_space c : c~Char
    let n = char.code c
    n == 9 or n == 10 or n == 12 or n == 13 or char.is_space_separator c

# The UTF-8 bytes of character `n`.
fn encode_char c -> r : c~Char, r~Bytes
    string.bytes (string.from_char c)

# ── Character references and escapes ─────────────────────────────────────────

# The characters numeric character reference `n` stands for: U+FFFD for 0, a
# surrogate or a number too large, and HTML's replacements for the C1
# controls that Windows-1252 has characters for.
fn code_point n -> r : n~Nat, r~Bytes
    let m = c1 n
    if n == 0 or m >= 0x110000 or (m >= 0xD800 and m < 0xE000)
        b"\xEF\xBF\xBD"
    else
        encode_char (char.from_scalar m)

fn c1 n -> r : n~Nat, r~Nat
    if n < 0x80 or n > 0x9F
        n
    else
        match list.head (list.map (\(_, v) -> v) (filter_c1 n C1))
            Some v -> v
            None   -> n

fn filter_c1 n ps -> r : n~Nat, ps~List (Nat, Nat), r~List (Nat, Nat)
    match ps
        []           -> []
        (k, v) :: rs -> if k == n then [(k, v)] else filter_c1 n rs

let C1 = [(0x80, 0x20AC), (0x82, 0x201A), (0x83, 0x0192), (0x84, 0x201E), (0x85, 0x2026), (0x86, 0x2020),
          (0x87, 0x2021), (0x88, 0x02C6), (0x89, 0x2030), (0x8A, 0x0160), (0x8B, 0x2039), (0x8C, 0x0152),
          (0x8E, 0x017D), (0x91, 0x2018), (0x92, 0x2019), (0x93, 0x201C), (0x94, 0x201D), (0x95, 0x2022),
          (0x96, 0x2013), (0x97, 0x2014), (0x98, 0x02DC), (0x99, 0x2122), (0x9A, 0x0161), (0x9B, 0x203A),
          (0x9C, 0x0153), (0x9E, 0x017E), (0x9F, 0x0178)]

# A character reference at `i` (`&amp;`, `&#35;`, `&#x22;`): what it stands
# for, and where it ends. An unknown name isn't one.
fn entity_at b i -> r : b~Bytes, i~Nat, r~Option (Bytes, Nat)
    if at b i != 38
        None
    else if at b (i + 1) == 35
        let hex = lower (at b (i + 2)) == 120
        let first = if hex then i + 3 else i + 2
        let stop = if hex then skip is_hex b first else skip is_digit b first
        let count = sub stop first
        if count >= 1 and (if hex then count <= 6 else count <= 7) and at b stop == 59
            Some (code_point (number b first stop (if hex then 16 else 10) 0), stop + 1)
        else
            None
    else if is_letter (at b (i + 1))
        let stop = skip is_alnum b (i + 1)
        if sub stop (i + 1) >= 2 and sub stop (i + 1) <= 32 and at b stop == 59
            match html.entity (text_of (part b (i + 1) stop))
                Some s -> Some (string.bytes s, stop + 1)
                None   -> None
        else
            None
    else
        None

# The number written in base `base` from `i` to `j`.
fn number b i j base acc -> r : b~Bytes, i~Nat, j~Nat, base~Nat, acc~Nat, r~Nat
    if i < j and i < len b
        let c = lower b[i]
        let d = if is_digit c then c - 48 else sub c 87
        number b (i + 1) j base (acc * base + d)
    else
        acc

# `b` with its backslash escapes and character references replaced.
fn unescape b -> r : b~Bytes, r~Bytes
    joined (unescape_from b 0 0 [])

fn unescape_from b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    decreasing sub (len b) i
    if i < len b
        if b[i] == 92 and is_escapable (at b (i + 1))
            unescape_from b (i + 2) (i + 2) (part b (i + 1) (i + 2) :: part b start i :: acc)
        else if b[i] == 38
            match entity_at b i
                Some (s, stop) if stop > i -> unescape_from b stop stop (s :: part b start i :: acc)
                _ -> unescape_from b start (i + 1) acc
        else
            unescape_from b start (i + 1) acc
    else
        part b start (len b) :: acc

# ── URLs ─────────────────────────────────────────────────────────────────────

# A link's destination percent-encoded: each byte that isn't a letter, a
# digit or one of `;/?:@&=+$,-_.!~*'()#` as `%XX`, except a `%` that already
# starts one.
fn encode_url b -> r : b~Bytes, r~Bytes
    joined (encode_from b 0 [])

fn encode_from b i acc -> r : b~Bytes, i~Nat, acc~List Bytes, r~List Bytes
    decreasing sub (len b) i
    if i < len b
        let c = b[i]
        if c == 37 and is_hex (at b (i + 1)) and is_hex (at b (i + 2))
            encode_from b (i + 3) (part b i (i + 3) :: acc)
        else if is_alnum c or url_safe c
            encode_from b (i + 1) (part b i (i + 1) :: acc)
        else
            encode_from b (i + 1) (percent c :: acc)
    else
        acc

fn url_safe c : c~Nat
    c == ';' or c == '/' or c == '?' or c == ':' or c == '@' or c == '&' or c == '=' or c == '+' or c == '$'
        or c == ',' or c == '-' or c == '_' or c == '.' or c == '!' or c == '~' or c == '*' or c == '\''
        or c == '(' or c == ')' or c == '#'

fn percent c -> r : c~Nat, r~Bytes
    let digits = b"0123456789ABCDEF"
    let hi = c / 16 % 16
    let lo = c % 16
    bytes.concat [b"%", part digits hi (hi + 1), part digits lo (lo + 1)]

# ── Link parts ───────────────────────────────────────────────────────────────

# Spaces, then at most one line ending, then spaces: where they end.
fn spnl b i -> r : b~Bytes, i~Nat, r~Nat
    let j = skip_byte 32 b i
    if at b j == 10 then skip_byte 32 b (j + 1) else j

# A link label at `i`, `[` to `]`, with at most 999 characters between and no
# unescaped bracket: where it ends.
fn link_label b i -> r : b~Bytes, i~Nat, r~Option Nat
    if at b i == 91 then label_from b (i + 1) 0 else None

fn label_from b i n -> r : b~Bytes, i~Nat, n~Nat, r~Option Nat
    if n > 999 or i >= len b
        None
    else
        let c = b[i]
        if c == 93
            Some (i + 1)
        else if c == 91
            None
        else if c == 92 and i + 1 < len b
            label_from b (i + 2) (n + 1 + counts b[i + 1])
        else
            label_from b (i + 1) (n + counts c)

# Whether byte `c` starts a character (UTF-16 code units, as JavaScript
# counts a label's length, but characters are close enough).
fn counts c -> r : c~Nat, r~Nat
    if c >= 0x80 and c < 0xC0 then 0 else 1

# A link destination at `i`: `<…>`, or bytes with balanced parentheses and
# no space or control character. Its text, unescaped and encoded, and where
# it ends.
fn destination b i -> r : b~Bytes, i~Nat, r~Option (Bytes, Nat)
    if at b i == 60
        match angled b (i + 1)
            Some stop -> Some (encode_url (unescape (part b (i + 1) stop)), stop + 1)
            None      -> None
    else
        match bare b i 0
            Some stop -> if stop == i and at b stop != 41 then None else Some (encode_url (unescape (part b i stop)), stop)
            None      -> None

fn angled b i -> r : b~Bytes, i~Nat, r~Option Nat
    if i < len b
        let c = b[i]
        if c == 62
            Some i
        else if c == 60 or c == 10
            None
        else if c == 92 and i + 1 < len b and b[i + 1] != 10
            angled b (i + 2)
        else
            angled b (i + 1)
    else
        None

fn bare b i depth -> r : b~Bytes, i~Nat, depth~Nat, r~Option Nat
    if i < len b
        let c = b[i]
        if c == 92 and is_escapable (at b (i + 1))
            bare b (i + 2) depth
        else if c == 40
            bare b (i + 1) (depth + 1)
        else if c == 41
            if depth == 0 then Some i else bare b (i + 1) (depth - 1)
        else if is_ascii_space c
            if depth == 0 then Some i else None
        else
            bare b (i + 1) depth
    else
        if depth == 0 then Some i else None

# A link title at `i`, in `"…"`, `'…'` or `(…)`: its text, unescaped, and
# where it ends.
fn title b i -> r : b~Bytes, i~Nat, r~Option (Bytes, Nat)
    let open = at b i
    let close = if open == 40 then 41 else open
    if open == 34 or open == 39 or open == 40
        match title_end b (i + 1) open close
            Some stop -> Some (unescape (part b (i + 1) stop), stop + 1)
            None      -> None
    else
        None

fn title_end b i open close -> r : b~Bytes, i~Nat, open~Nat, close~Nat, r~Option Nat
    if i < len b
        let c = b[i]
        if c == close
            Some i
        else if c == 92 and i + 1 < len b
            title_end b (i + 2) open close
        else if open == 40 and c == 40
            None
        else
            title_end b (i + 1) open close
    else
        None

# ── Raw HTML ─────────────────────────────────────────────────────────────────

# An HTML tag at `i` as CommonMark recognizes one (an open or closing tag, a
# comment, a processing instruction, a declaration or a CDATA section):
# where it ends.
fn html_tag b i -> r : b~Bytes, i~Nat, r~Option Nat
    if at b i != 60
        None
    else
        let c = at b (i + 1)
        if is_letter c
            open_tag b (i + 1)
        else if c == 47
            close_tag b (i + 2)
        else if c == 63
            match find b b"?>" (i + 2)
                Some k -> Some (k + 2)
                None   -> None
        else if c == 33
            if bytes.matches_at b (i + 2) b"-->"
                Some (i + 5)
            else if bytes.matches_at b (i + 2) b"--->"
                Some (i + 6)
            else if bytes.matches_at b (i + 2) b"--"
                match find b b"-->" (i + 4)
                    Some k -> Some (k + 3)
                    None   -> None
            else if bytes.matches_at b (i + 2) b"[CDATA["
                match find b b"]]>" (i + 9)
                    Some k -> Some (k + 3)
                    None   -> None
            else if is_letter (at b (i + 2))
                match find b b">" (i + 3)
                    Some k -> Some (k + 1)
                    None   -> None
            else
                None
        else
            None

fn is_tag_char c : c~Nat
    is_alnum c or c == 45

# An open tag's name at `i`, then its attributes, `/` and `>`.
fn open_tag b i -> r : b~Bytes, i~Nat, r~Option Nat
    attributes b (skip is_tag_char b i) (len b)

# `fuel` bounds the attributes left: each takes at least a byte.
fn attributes b i fuel -> r : b~Bytes, i~Nat, fuel~Nat, r~Option Nat
    decreasing fuel
    let j = skip is_ascii_space b i
    let c = at b j
    if c == 62
        Some (j + 1)
    else if c == 47
        if at b (j + 1) == 62 then Some (j + 2) else None
    else if j > i and (is_letter c or c == 95 or c == 58)
        match attribute_value b (skip is_attribute_char b j)
            Some k if fuel > 0 -> attributes b k (fuel - 1)
            _ -> None
    else
        None

fn is_attribute_char c : c~Nat
    is_alnum c or c == 95 or c == 58 or c == 46 or c == 45

# After an attribute's name: `= value`, if any, and where it ends.
fn attribute_value b i -> r : b~Bytes, i~Nat, r~Option Nat
    let j = skip is_ascii_space b i
    if at b j != 61
        Some i
    else
        let k = skip is_ascii_space b (j + 1)
        let c = at b k
        if c == 34 or c == 39
            match find b (part b k (k + 1)) (k + 1)
                Some e -> Some (e + 1)
                None   -> None
        else
            let e = skip is_unquoted b k
            if e > k then Some e else None

fn is_unquoted c : c~Nat
    c > 32 and c != 34 and c != 39 and c != 61 and c != 60 and c != 62 and c != 96 and c != 256

fn close_tag b i -> r : b~Bytes, i~Nat, r~Option Nat
    if is_letter (at b i)
        let j = skip is_ascii_space b (skip is_tag_char b i)
        if at b j == 62 then Some (j + 1) else None
    else
        None

# ── Blocks ───────────────────────────────────────────────────────────────────
# Each line of the text, in turn, continues the blocks still open (a block
# quote's `>`, a list item's indentation, …), may start new ones, and then
# goes to the innermost open block that takes lines, or starts a paragraph.
# The open blocks are a list, innermost first, the document last; a block
# that is closed goes into its parent's children.

# A list's kind, and one item's marker.
record ListData
    ordered~Bool
    mark~Nat          # the bullet (`-`, `+`, `*`), or the delimiter after the number (`.`, `)`)
    start~Nat
    offset~Nat        # the marker's columns from where the container's content starts
    padding~Nat       # the columns from the marker to the item's content

enum Kind
    KDoc
    KQuote
    KList data                : data~ListData
    KItem data                : data~ListData
    KHeading level            : level~Nat
    KBreak
    KFence mark length indent : mark~Nat, length~Nat, indent~Nat
    KIndented
    KHtml kind                : kind~Nat
    KPara

# A piece of a leaf block's text: one line's rest, with its line ending.
# Its bytes start with `pad` spaces that stand for part of a tab; the rest
# start at `at` in the source.
record Seg
    at~Nat
    pad~Nat
    text~Bytes

# Where a closed block is: its first and last lines, and its bytes.
record Where
    first~Nat
    last~Nat
    start~Nat
    stop~Nat

# A closed block, before its text is parsed for inlines.
enum Raw
    RPara segs w             : segs~List Seg, w~Where
    RHeading level segs w    : level~Nat, segs~List Seg, w~Where
    RBreak w                 : w~Where
    RQuote children w        : children~List Raw, w~Where
    RList data tight items w : data~ListData, tight~Bool, items~List Raw, w~Where
    RItem children w         : children~List Raw, w~Where
    RCode fenced info segs w : fenced~Bool, info~Bytes, segs~List Seg, w~Where
    RHtml segs w             : segs~List Seg, w~Where

# An open block: what it is, where it started, its text so far and its
# closed children (both last first).
record Open
    kind~Kind
    first~Nat
    start~Nat
    segs~List Seg
    children~List Raw

# Where the line being read is: its bytes from `start` to `stop` (without
# its line ending), how far it has been read (`offset`, and the column,
# tabs every 4), and whether a tab is partly read.
record Ln
    start~Nat
    stop~Nat
    offset~Nat
    column~Nat
    in_tab~Bool

# The block parser's state.
record S
    opens~List Open     # innermost first, the document last
    line~Nat            # the line's number, from 1
    prev~Nat            # where the line before it ended
    ln~Ln
    container~Nat       # the depth of the block new ones go into (the document's is 0)
    matched~Nat         # the depth of the innermost block this line continues
    closed~Bool         # whether the blocks this line didn't continue are closed

fn where_of r -> w : r~Raw, w~Where
    match r
        RPara _ w      -> w
        RHeading _ _ w -> w
        RBreak w       -> w
        RQuote _ w     -> w
        RList _ _ _ w  -> w
        RItem _ w      -> w
        RCode _ _ _ w  -> w
        RHtml _ w      -> w

fn depth opens -> d : opens~List Open, d~Nat
    sub (list.length opens) 1

# The open block at depth `d`.
fn open_at opens d -> r : opens~List Open, d~Nat, r~Option Open
    list.head (list.drop (sub (list.length opens) (d + 1)) opens)

fn kind_at opens d -> r : opens~List Open, d~Nat, r~Kind
    match open_at opens d
        Some o -> o.kind
        None   -> KDoc

fn tip_kind opens -> r : opens~List Open, r~Kind
    match opens
        o :: _ -> o.kind
        []     -> KDoc

fn is_para k : k~Kind
    match k
        KPara -> True
        _     -> False

fn is_list k : k~Kind
    match k
        KList _ -> True
        _       -> False

fn accepts_lines k : k~Kind
    match k
        KFence _ _ _ -> True
        KIndented    -> True
        KHtml _      -> True
        KPara        -> True
        _            -> False

fn is_item k : k~Kind
    match k
        KItem _ -> True
        _       -> False

fn can_contain parent child : parent~Kind, child~Kind
    match parent
        KDoc    -> not (is_item child)
        KQuote  -> not (is_item child)
        KItem _ -> not (is_item child)
        KList _ -> is_item child
        _       -> False

# The byte at `i` of the line, or 256 past its end.
fn pk src ln i -> r : src~Bytes, ln~Ln, i~Nat, r~Nat
    if i < ln.stop then at src i else 256

# Where the line's next byte other than a space or a tab is, and its column.
fn nonspace src ln -> r : src~Bytes, ln~Ln, r~(Nat, Nat)
    nonspace_from src ln.stop ln.offset ln.column

fn nonspace_from src stop i col -> r : src~Bytes, stop~Nat, i~Nat, col~Nat, r~(Nat, Nat)
    if i < stop and i < len src and src[i] == 32
        nonspace_from src stop (i + 1) (col + 1)
    else if i < stop and i < len src and src[i] == 9
        nonspace_from src stop (i + 1) (col + 4 - col % 4)
    else
        (i, col)

fn with_offset ln offset column in_tab -> r : ln~Ln, offset~Nat, column~Nat, in_tab~Bool, r~Ln
    Ln ln.start ln.stop offset column in_tab

# Read `count` more of the line: columns if `columns` (a tab may be read in
# part), else bytes.
fn advance src ln count columns -> r : src~Bytes, ln~Ln, count~Nat, columns~Bool, r~Ln
    if count > 0 and ln.offset < ln.stop
        if at src ln.offset == 9
            let to_tab = 4 - ln.column % 4
            if columns
                let in_tab = to_tab > count
                let step = min to_tab count
                let off = if in_tab then ln.offset else ln.offset + 1
                advance src (with_offset ln off (ln.column + step) in_tab) (count - step) columns
            else
                advance src (with_offset ln (ln.offset + 1) (ln.column + to_tab) False) (count - 1) columns
        else
            advance src (with_offset ln (ln.offset + 1) (ln.column + 1) False) (count - 1) columns
    else
        ln

fn advance_nonspace src ln -> r : src~Bytes, ln~Ln, r~Ln
    match nonspace src ln
        (i, col) -> with_offset ln i col False

fn to_end ln -> r : ln~Ln, r~Ln
    with_offset ln ln.stop ln.column False

fn with_ln s ln -> r : s~S, ln~Ln, r~S
    S s.opens s.line s.prev ln s.container s.matched s.closed

fn with_opens s opens -> r : s~S, opens~List Open, r~S
    S opens s.line s.prev s.ln (depth opens) s.matched s.closed

# Close the innermost open block, ending at `last` (a line) and `stop`.
fn close opens last stop -> r : opens~List Open, last~Nat, stop~Nat, r~List Open
    match opens
        o :: p :: rest -> Open p.kind p.first p.start p.segs (finish o last stop :: p.children) :: rest
        _              -> opens

# Close open blocks until `d` is the deepest.
fn close_to opens d last stop -> r : opens~List Open, d~Nat, last~Nat, stop~Nat, r~List Open
    match opens
        _ :: _ :: _ ->
            if depth opens > d then close_to (close opens last stop) d last stop else opens
        _           -> opens

# Close the blocks this line doesn't continue, once.
fn close_unmatched s -> r : s~S, r~S
    if s.closed
        s
    else
        let opens = close_to s.opens s.matched (sub s.line 1) s.prev
        S opens s.line s.prev s.ln (depth opens) s.matched True

# Open a block of kind `k` at `start`, closing the innermost ones until one
# can contain it.
fn add_child s k start -> r : s~S, k~Kind, start~Nat, r~S
    let opens = make_room s.opens k (sub s.line 1) s.prev
    with_opens s (Open k s.line start [] [] :: opens)

fn make_room opens k last stop -> r : opens~List Open, k~Kind, last~Nat, stop~Nat, r~List Open
    match opens
        o :: _ :: _ -> if can_contain o.kind k then opens else make_room (close opens last stop) k last stop
        _           -> opens

# A closed block of what was open.
fn finish o last stop -> r : o~Open, last~Nat, stop~Nat, r~Raw
    let w = Where o.first last o.start stop
    let children = list.reverse o.children
    let segs = list.reverse o.segs
    match o.kind
        KPara          -> RPara segs w
        KHeading level -> RHeading level segs w
        KBreak         -> RBreak w
        KDoc           -> RQuote children w
        KQuote         -> RQuote children w
        KList data     ->
            let w2 = match list.head o.children
                Some c -> Where o.first (where_of c).last o.start (where_of c).stop
                None   -> w
            RList data (tight children) children w2
        KItem _        ->
            match list.head o.children
                Some c -> RItem children (Where o.first (where_of c).last o.start (where_of c).stop)
                None   -> RItem children (Where o.first o.first o.start o.start)
        KFence _ _ _   ->
            match segs
                s :: rest -> RCode True (trim (unescape (without_newline s.text))) rest w
                []        -> RCode True b"" [] w
        KIndented      ->
            let kept = list.reverse (drop_blank o.segs)
            let n = list.length kept
            match list.head (drop_blank o.segs)
                Some s -> RCode False b"" kept (Where o.first (o.first + sub n 1) o.start (s.at + sub (len s.text) (s.pad + 1)))
                None   -> RCode False b"" kept w
        KHtml _        -> RHtml segs w

fn without_newline b -> r : b~Bytes, r~Bytes
    if len b > 0 and b[len b - 1] == 10 then bytes.slice b 0 (len b - 1) else b

# Without the blank lines at the start (the end of an indented code block).
fn drop_blank segs -> r : segs~List Seg, r~List Seg
    match segs
        s :: rest -> if blank_bytes s.text then drop_blank rest else segs
        []        -> []

fn blank_bytes b : b~Bytes
    skip is_ascii_space b 0 >= len b

# Whether a list's items are separated by no blank line, nor are the
# blocks directly in each item.
fn tight items : items~List Raw
    match items
        a :: rest ->
            let apart = match list.head rest
                Some b -> (where_of a).last + 1 != (where_of b).first
                None   -> False
            not apart and tight_children (children_of a) and tight rest
        []        -> True

fn tight_children cs : cs~List Raw
    match cs
        a :: rest ->
            match list.head rest
                Some b -> (where_of a).last + 1 == (where_of b).first and tight_children rest
                None   -> True
        []        -> True

fn children_of r -> cs : r~Raw, cs~List Raw
    match r
        RItem cs _ -> cs
        _          -> []

# Add the rest of the line to the innermost block.
fn add_line src s -> r : src~Bytes, s~S, r~S
    let ln = s.ln
    let pad = if ln.in_tab then 4 - ln.column % 4 else 0
    let off = if ln.in_tab then ln.offset + 1 else ln.offset
    let text = bytes.concat [part b"    " 0 pad, clean (part src off ln.stop), b"\n"]
    match s.opens
        o :: rest -> with_opens s (Open o.kind o.first o.start (Seg off pad text :: o.segs) o.children :: rest)
        []        -> s

# ── Continuing blocks ────────────────────────────────────────────────────────

enum Cont
    Matched ln : ln~Ln
    Failed
    Done ln    : ln~Ln

# Whether the line continues an open block of kind `k` (`has_child`: whether
# it has any children), reading what that takes.
fn continues src k has_child ln -> r : src~Bytes, k~Kind, has_child~Bool, ln~Ln, r~Cont
    match nonspace src ln
        (nn, nncol) ->
            let indent = sub nncol ln.column
            let blank = nn >= ln.stop
            match k
                KQuote                          ->
                    if indent < 4 and pk src ln nn == 62
                        Matched (after_quote_marker src ln)
                    else
                        Failed
                KItem d                         ->
                    if indent >= d.offset + d.padding
                        Matched (advance src ln (d.offset + d.padding) True)
                    else if blank and has_child
                        Matched (advance_nonspace src ln)
                    else
                        Failed
                KFence mark length fence_indent ->
                    if indent <= 3 and pk src ln nn == mark and closing_fence src ln nn mark >= length
                        Done (to_end ln)
                    else
                        Matched (skip_indent src ln fence_indent)
                KIndented                       ->
                    if indent >= 4
                        Matched (advance src ln 4 True)
                    else if blank
                        Matched (advance_nonspace src ln)
                    else
                        Failed
                KHtml t                         -> if blank and (t == 6 or t == 7) then Failed else Matched ln
                KPara                           -> if blank then Failed else Matched ln
                KHeading _                      -> Failed
                KBreak                          -> Failed
                _                               -> Matched ln

fn after_quote_marker src ln -> r : src~Bytes, ln~Ln, r~Ln
    let l2 = advance src (advance_nonspace src ln) 1 False
    if is_space_or_tab (pk src l2 l2.offset) then advance src l2 1 True else l2

# Up to `n` columns of spaces or tabs.
fn skip_indent src ln n -> r : src~Bytes, ln~Ln, n~Nat, r~Ln
    if n > 0 and is_space_or_tab (pk src ln ln.offset) then skip_indent src (advance src ln 1 True) (n - 1) else ln

# A closing code fence at `i`, of `mark`s: how many, if only spaces and tabs
# follow; else 0.
fn closing_fence src ln i mark -> r : src~Bytes, ln~Ln, i~Nat, mark~Nat, r~Nat
    let e = skip_byte mark src i
    let n = sub e i
    if n >= 3 and rest_blank src ln e then n else 0

# Whether only spaces and tabs are left on the line from `i`.
fn rest_blank src ln i : src~Bytes, ln~Ln, i~Nat
    skip is_space_or_tab src i >= ln.stop

enum Walk
    WAt d ln : d~Nat, ln~Ln
    WDone ln : ln~Ln

# Continue the open blocks `path` (outermost first), the first at depth `d`
# of `tip`: how deep the line goes.
fn walk src path d tip ln -> r : src~Bytes, path~List Open, d~Nat, tip~Nat, ln~Ln, r~Walk
    match path
        o :: rest ->
            let has_child = d < tip or not (list.length o.children == 0)
            match continues src o.kind has_child ln
                Matched l2 -> walk src rest (d + 1) tip l2
                Failed     -> WAt (sub d 1) ln
                Done l2    -> WDone l2
        []        -> WAt (sub d 1) ln

# ── Starting blocks ──────────────────────────────────────────────────────────

enum Start
    NoStart
    Container s : s~S
    Leaf s      : s~S

# A character that may start a block, other than indented code.
fn maybe_special c : c~Nat
    c == 35 or c == 96 or c == 126 or c == 42 or c == 43 or c == 95 or c == 61 or c == 60 or c == 62
        or c == 45 or is_digit c

# Start the blocks the line starts, inside the container, while they are
# containers.
fn starts src s fuel -> r : src~Bytes, s~S, fuel~Nat, r~S
    decreasing fuel
    let k = kind_at s.opens s.container
    if fuel == 0 or (accepts_lines k and not (is_para k))
        s
    else
        match nonspace src s.ln
            (nn, nncol) ->
                let indent = sub nncol s.ln.column
                if indent < 4 and not (maybe_special (pk src s.ln nn))
                    with_ln s (advance_nonspace src s.ln)
                else
                    match start src s k nn indent
                        Container s2 -> starts src s2 (fuel - 1)
                        Leaf s2      -> s2
                        NoStart      -> with_ln s (advance_nonspace src s.ln)

fn start src s k nn indent -> r : src~Bytes, s~S, k~Kind, nn~Nat, indent~Nat, r~Start
    let ln = s.ln
    let c = pk src ln nn
    let blank = nn >= ln.stop
    if indent >= 4
        if not (is_para (tip_kind s.opens)) and not blank
            let s2 = close_unmatched (with_ln s (advance src ln 4 True))
            Leaf (add_child s2 KIndented s2.ln.offset)
        else
            NoStart
    else if c == 62
        let s2 = close_unmatched (with_ln s (after_quote_marker src ln))
        Container (add_child s2 KQuote nn)
    else if c == 35
        atx src s nn
    else if (c == 96 or c == 126) and fence src ln nn c >= 3
        let n = fence src ln nn c
        let s2 = close_unmatched (with_ln s (advance src (advance_nonspace src ln) n False))
        Leaf (add_child s2 (KFence c n indent) nn)
    else
        let lazy = not s.closed and not blank and is_para (tip_kind s.opens)
        let t = html_start src ln nn (not (is_para k) and not lazy)
        if t > 0
            let s2 = close_unmatched s
            Leaf (add_child s2 (KHtml t) ln.offset)
        else
            let heading = if is_para k and setext src ln nn > 0 then setext_heading src s (setext src ln nn) else NoStart
            match heading
                NoStart ->
                    if thematic_break src ln nn
                        let s2 = close_unmatched (with_ln s (to_end ln))
                        Leaf (add_child s2 KBreak nn)
                    else
                        list_item src s k nn indent
                _       -> heading

# An ATX heading: `#` to `######`, then a space, a tab or the line's end.
fn atx src s nn -> r : src~Bytes, s~S, nn~Nat, r~Start
    let ln = s.ln
    let e = skip_byte 35 src nn
    let level = sub e nn
    if level <= 6 and (e >= ln.stop or is_space_or_tab (pk src ln e))
        let content_start = min (skip is_space_or_tab src e) ln.stop
        let s2 = close_unmatched (with_ln s (to_end ln))
        let s3 = add_child s2 (KHeading level) nn
        let text = atx_content (clean (part src content_start ln.stop))
        match s3.opens
            o :: rest -> Leaf (with_opens s3 (Open o.kind o.first o.start [Seg content_start 0 text] [] :: rest))
            []        -> NoStart
    else
        NoStart

# A heading's text without its closing `#`s.
fn atx_content b -> r : b~Bytes, r~Bytes
    let e = trim_end is_space_or_tab b (len b) 0
    let h = trim_end (\c -> c == 35) b e 0
    if h == e
        b
    else
        let s = trim_end is_space_or_tab b h 0
        if s == 0 then b"" else if s < h then part b 0 s else b

# An opening code fence at `i` of `c`s: how many (none if a backtick fence's
# info string has a backtick).
fn fence src ln i c -> r : src~Bytes, ln~Ln, i~Nat, c~Nat, r~Nat
    let e = min (skip_byte c src i) ln.stop
    if c == 96 and find (part src e ln.stop) b"`" 0 != None then 0 else sub e i

# A setext heading's underline at `i`: its level, or 0.
fn setext src ln i -> r : src~Bytes, ln~Ln, i~Nat, r~Nat
    let c = pk src ln i
    if c == 61 or c == 45
        let e = skip_byte c src i
        if rest_blank src ln e then (if c == 61 then 1 else 2) else 0
    else
        0

# Three or more `*`, `-` or `_`, with only spaces and tabs between and after.
fn thematic_break src ln i : src~Bytes, ln~Ln, i~Nat
    let c = pk src ln i
    (c == 42 or c == 45 or c == 95) and break_count src ln i c 0 >= 3

fn break_count src ln i c n -> r : src~Bytes, ln~Ln, i~Nat, c~Nat, n~Nat, r~Nat
    if i < ln.stop and i < len src
        if src[i] == c
            break_count src ln (i + 1) c (n + 1)
        else if is_space_or_tab src[i]
            break_count src ln (i + 1) c n
        else
            0
    else
        n

# The paragraph that is the container becomes a heading; the link reference
# definitions it starts with stay a paragraph before it.
fn setext_heading src s level -> r : src~Bytes, s~S, level~Nat, r~Start
    let s2 = close_unmatched s
    match s2.opens
        o :: rest ->
            let content = seg_bytes o.segs
            let refs = definitions_length content 0 (len content)
            if len content > refs
                let segs = list.reverse o.segs
                let heading_segs = drop_bytes segs refs
                let ref_segs = take_bytes segs refs
                let ref_lines = list.length ref_segs
                let before = if refs > 0
                    close (Open KPara o.first o.start (list.reverse ref_segs) [] :: rest) (o.first + sub ref_lines 1) (seg_end ref_segs o.start)
                else
                    rest
                let start = match heading_segs
                    h :: _ -> h.at
                    []     -> o.start
                let heading = Open (KHeading level) (o.first + ref_lines) start (list.reverse heading_segs) []
                Leaf (with_opens (with_ln s2 (to_end s2.ln)) (heading :: before))
            else
                NoStart
        []        -> NoStart

# The segments' bytes, in order (they are kept last first).
fn seg_bytes segs -> r : segs~List Seg, r~Bytes
    bytes.concat (list.reverse (list.map (\g -> g.text) segs))

# The segments that make up the first `n` bytes (whole lines).
fn take_bytes segs n -> r : segs~List Seg, n~Nat, r~List Seg
    match segs
        g :: rest -> if n > 0 then g :: take_bytes rest (sub n (len g.text)) else []
        []        -> []

fn drop_bytes segs n -> r : segs~List Seg, n~Nat, r~List Seg
    match segs
        g :: rest -> if n > 0 then drop_bytes rest (sub n (len g.text)) else segs
        []        -> []

# Where the last of the segments ends in the source (before its line ending).
fn seg_end segs dflt -> r : segs~List Seg, dflt~Nat, r~Nat
    match list.head (list.reverse segs)
        Some g -> g.at + sub (len g.text) (g.pad + 1)
        None   -> dflt

# How many bytes the link reference definitions at the start of `b` take.
fn definitions_length b i fuel -> r : b~Bytes, i~Nat, fuel~Nat, r~Nat
    decreasing fuel
    match reference b i
        Some d if fuel > 0 and d.stop > i -> definitions_length b d.stop (fuel - 1)
        _ -> i

# A list item's marker, then up to 4 spaces: the item, and the list if the
# marker doesn't continue the innermost one.
fn list_item src s k nn indent -> r : src~Bytes, s~S, k~Kind, nn~Nat, indent~Nat, r~Start
    match list_marker src s.ln k nn indent
        Some (data, ln) ->
            let s2 = close_unmatched (with_ln s ln)
            let s3 = match tip_kind s2.opens
                KList d -> if same_list d data then s2 else add_child s2 (KList data) nn
                _       -> add_child s2 (KList data) nn
            Container (add_child s3 (KItem data) nn)
        None            -> NoStart

fn same_list a b : a~ListData, b~ListData
    a.ordered == b.ordered and a.mark == b.mark

fn list_marker src ln k nn indent -> r : src~Bytes, ln~Ln, k~Kind, nn~Nat, indent~Nat, r~Option (ListData, Ln)
    let c = pk src ln nn
    let digits = sub (min (skip is_digit src nn) ln.stop) nn
    let delim = pk src ln (nn + digits)
    let bullet = c == 45 or c == 43 or c == 42
    let number = number src nn (nn + digits) 10 0
    let ordered = not bullet and digits >= 1 and digits <= 9 and (delim == 46 or delim == 41)
                  and (not (is_para k) or number == 1)
    let size = if bullet then 1 else digits + 1
    let after = pk src ln (nn + size)
    if indent >= 4 or not (bullet or ordered) or not (after == 256 or is_space_or_tab after)
        None
    else if is_para k and rest_blank src ln (nn + size)
        None
    else
        let l1 = advance src (advance_nonspace src ln) size True
        let l2 = spaces_after src (advance src l1 1 True) l1.column 5
        let spaces = sub l2.column l1.column
        if spaces >= 5 or spaces < 1 or pk src l2 l2.offset == 256
            let l3 = with_offset l1 l1.offset l1.column l1.in_tab
            let l4 = if is_space_or_tab (pk src l3 l3.offset) then advance src l3 1 True else l3
            Some (ListData ordered (if bullet then c else delim) number indent (size + 1), l4)
        else
            Some (ListData ordered (if bullet then c else delim) number indent (size + spaces), l2)

# Read single columns of spaces and tabs while fewer than 5 have been
# read since column `from` (`fuel` bounds them).
fn spaces_after src ln from fuel -> r : src~Bytes, ln~Ln, from~Nat, fuel~Nat, r~Ln
    decreasing fuel
    if fuel > 0 and sub ln.column from < 5 and is_space_or_tab (pk src ln ln.offset)
        spaces_after src (advance src ln 1 True) from (fuel - 1)
    else
        ln

# ── HTML blocks ──────────────────────────────────────────────────────────────

let HTML_RAW = [b"script", b"pre", b"textarea", b"style"]

let HTML_BLOCKS = [b"address", b"article", b"aside", b"base", b"basefont", b"blockquote", b"body", b"caption",
                   b"center", b"col", b"colgroup", b"dd", b"details", b"dialog", b"dir", b"div", b"dl", b"dt",
                   b"fieldset", b"figcaption", b"figure", b"footer", b"form", b"frame", b"frameset", b"h1", b"h2",
                   b"h3", b"h4", b"h5", b"h6", b"head", b"header", b"hr", b"html", b"iframe", b"legend", b"li",
                   b"link", b"main", b"menu", b"menuitem", b"nav", b"noframes", b"ol", b"optgroup", b"option", b"p",
                   b"param", b"search", b"section", b"summary", b"table", b"tbody", b"td", b"tfoot", b"th",
                   b"thead", b"title", b"tr", b"track", b"ul"]

# The kind of HTML block the line starts at `i` (1 to 7, as the spec numbers
# them), or 0; kind 7 only if `seven` (it can't interrupt a paragraph).
fn html_start src ln i seven -> r : src~Bytes, ln~Ln, i~Nat, seven~Bool, r~Nat
    let line = part src i ln.stop
    if at line 0 != 60
        0
    else if tag_in line 1 HTML_RAW (\c -> is_ascii_space c or c == 62 or c == 256)
        1
    else if bytes.matches_at line 0 b"<!--"
        2
    else if at line 1 == 63
        3
    else if at line 1 == 33 and is_letter (at line 2)
        4
    else if bytes.matches_at line 0 b"<![CDATA["
        5
    else if block_tag line (if at line 1 == 47 then 2 else 1)
        6
    else if seven and complete_tag line
        7
    else
        0

# One of the block-level tags' names at `i`, then white space, `>`, `/>` or
# the end.
fn block_tag line i : line~Bytes, i~Nat
    let e = skip is_alnum line i
    let c = at line e
    tag_in line i HTML_BLOCKS (\x -> is_ascii_space x or x == 62 or x == 256 or x == 47)
        and (c != 47 or at line (e + 1) == 62)

# Whether one of `names` (lower case) is at `i`, ignoring case, followed by
# a byte that `after` accepts.
fn tag_in line i names after : line~Bytes, i~Nat, names~List Bytes, after~(Nat -> Bool)
    match names
        n :: rest -> (matches_lower line i n and after (at line (i + len n))) or tag_in line i rest after
        []        -> False

# An open or closing tag, then only white space.
fn complete_tag line : line~Bytes
    let stop = if at line 1 == 47 then close_tag line 2 else (if is_letter (at line 1) then open_tag line 1 else None)
    match stop
        Some e -> skip is_ascii_space line e >= len line
        None   -> False

# Whether the line ends an HTML block of kind `t` (1 to 5).
fn html_end line t : line~Bytes, t~Nat
    if t == 1
        has_close_tag line 0
    else if t == 2
        find line b"-->" 0 != None
    else if t == 3
        find line b"?>" 0 != None
    else if t == 4
        find line b">" 0 != None
    else if t == 5
        find line b"]]>" 0 != None
    else
        False

fn has_close_tag line i : line~Bytes, i~Nat
    if i < len line
        (bytes.matches_at line i b"</" and tag_in line (i + 2) HTML_RAW (\c -> c == 62)) or has_close_tag line (i + 1)
    else
        False

# ── Lines ────────────────────────────────────────────────────────────────────

# Read one line into the open blocks.
fn incorporate src s -> r : src~Bytes, s~S, r~S
    let tip = depth s.opens
    match walk src (list.drop 1 (list.reverse s.opens)) 1 tip s.ln
        WDone ln -> with_opens (with_ln s ln) (close s.opens s.line ln.stop)
        WAt m ln ->
            let s2 = starts src (S s.opens s.line s.prev ln m m (m == tip)) (sub ln.stop ln.start + 2)
            line_text src s2

# The rest of the line: a lazy continuation of a paragraph, or the
# innermost block's text, or a new paragraph.
fn line_text src s -> r : src~Bytes, s~S, r~S
    match nonspace src s.ln
        (nn, _) ->
            let blank = nn >= s.ln.stop
            if not s.closed and not blank and is_para (tip_kind s.opens)
                add_line src s
            else
                let s1 = close_unmatched s
                let k = tip_kind s1.opens
                if accepts_lines k
                    let s2 = add_line src s1
                    match k
                        KHtml t ->
                            if t <= 5 and html_end (part src s1.ln.offset s1.ln.stop) t
                                with_opens s2 (close s2.opens s2.line s2.ln.stop)
                            else
                                s2
                        _       -> s2
                else if s1.ln.offset < s1.ln.stop and not blank
                    let s2 = add_child s1 KPara nn
                    add_line src (with_ln s2 (advance_nonspace src s2.ln))
                else
                    s1

# Read the lines from `i`: each ends at a line feed, a carriage return, or
# both; a line ending at the very end doesn't start another line.
fn read_lines src i s -> r : src~Bytes, i~Nat, s~S, r~S
    if i < len src
        let e = skip (\c -> c != 10 and c != 13) src i
        let next = if at src e == 13 and at src (e + 1) == 10 then e + 2 else e + 1
        let s2 = incorporate src (S s.opens (s.line + 1) s.prev (Ln i e i 0 False) 0 0 True)
        read_lines src next (S s2.opens s2.line e s2.ln 0 0 True)
    else
        s

# The text's blocks, before their inlines.
fn raw_blocks src -> r : src~Bytes, r~List Raw
    let s = read_lines src 0 (S [Open KDoc 1 0 [] []] 0 0 (Ln 0 0 0 0 False) 0 0 True)
    match close_to s.opens 0 s.line s.prev
        d :: _ -> list.reverse d.children
        []     -> []

# ── Link reference definitions ───────────────────────────────────────────────

# A definition, with its label normalized for matching.
record Def
    key~String
    label~Bytes
    url~Bytes
    title~Option Bytes
    stop~Nat

# A link reference definition at `i`: `[label]:`, a destination, maybe a
# title, and nothing else on the line.
fn reference b i -> r : b~Bytes, i~Nat, r~Option Def
    match link_label b i
        Some j if at b j == 58 ->
            let label = part b (i + 1) (sub j 1)
            let key = label_key (text_of label)
            match destination b (spnl b (j + 1))
                Some (url, d) ->
                    let t = spnl b d
                    let titled = if t > d then title b t else None
                    let full = match titled
                        Some (tt, e) -> match line_end b e
                            Some stop -> Some (Def key label url (Some tt) stop)
                            None      -> None
                        None         -> None
                    let bare_def = match line_end b d
                        Some stop -> Some (Def key label url None stop)
                        None      -> None
                    if key == ""
                        None
                    else
                        match full
                            Some x -> Some x
                            None   -> bare_def
                None          -> None
        _ -> None

# Spaces, then a line ending or the end: where they end.
fn line_end b i -> r : b~Bytes, i~Nat, r~Option Nat
    let j = skip_byte 32 b i
    if j >= len b then Some j else if b[j] == 10 then Some (j + 1) else None

# The definitions a paragraph starts with, last first, and where they end.
fn take_definitions b i fuel acc -> r : b~Bytes, i~Nat, fuel~Nat, acc~List (Def, Nat), r~(List (Def, Nat), Nat)
    decreasing fuel
    match reference b i
        Some d if fuel > 0 and d.stop > i -> take_definitions b d.stop (fuel - 1) ((d, i) :: acc)
        _ -> (acc, i)

# Take the link reference definitions out of the paragraphs, in order: the
# blocks left, and the definitions (last first).
fn strip_definitions bs acc -> r : bs~List Raw, acc~List (Def, Span), r~(List Raw, List (Def, Span))
    match bs
        []                        -> ([], acc)
        RPara segs w :: rest      ->
            let content = bytes.concat (list.map (\g -> g.text) segs)
            match take_definitions content 0 (len content) []
                (found, used) ->
                    let acc2 = add_definitions segs found acc
                    let left = drop_bytes segs used
                    let lines = sub (list.length segs) (list.length left)
                    match strip_definitions rest acc2
                        (others, acc3) ->
                            if blank_bytes (bytes.concat (list.map (\g -> g.text) left))
                                (others, acc3)
                            else
                                let start = match left
                                    g :: _ -> g.at
                                    []     -> w.start
                                (RPara left (Where (w.first + lines) w.last start w.stop) :: others, acc3)
        RQuote cs w :: rest       ->
            match strip_definitions cs acc
                (cs2, acc2) -> match strip_definitions rest acc2
                    (others, acc3) -> (RQuote cs2 w :: others, acc3)
        RList d t items w :: rest ->
            match strip_definitions items acc
                (items2, acc2) -> match strip_definitions rest acc2
                    (others, acc3) -> (RList d t items2 w :: others, acc3)
        RItem cs w :: rest        ->
            match strip_definitions cs acc
                (cs2, acc2) -> match strip_definitions rest acc2
                    (others, acc3) -> (RItem cs2 w :: others, acc3)
        b :: rest                 ->
            match strip_definitions rest acc
                (others, acc2) -> (b :: others, acc2)

# The definitions found (last first), with their spans, onto `acc`.
fn add_definitions segs found acc -> r : segs~List Seg, found~List (Def, Nat), acc~List (Def, Span), r~List (Def, Span)
    match list.reverse found
        [] -> acc
        ds -> add_each segs ds acc

fn add_each segs ds acc -> r : segs~List Seg, ds~List (Def, Nat), acc~List (Def, Span), r~List (Def, Span)
    match ds
        (d, at) :: rest -> add_each segs rest ((d, Span (position (seg_map segs) at) (position (seg_map segs) (sub d.stop 1))) :: acc)
        []              -> acc

# Where each segment starts in the text made of them, in the source, and
# its padding.
fn seg_map segs -> r : segs~List Seg, r~List (Nat, Nat, Nat)
    seg_map_from segs 0

fn seg_map_from segs k -> r : segs~List Seg, k~Nat, r~List (Nat, Nat, Nat)
    match segs
        g :: rest -> (k, g.at, g.pad) :: seg_map_from rest (k + len g.text)
        []        -> []

# Where byte `p` of the segments' text is in the source.
fn position map p -> r : map~List (Nat, Nat, Nat), p~Nat, r~Nat
    position_from map p 0

fn position_from map p best -> r : map~List (Nat, Nat, Nat), p~Nat, best~Nat, r~Nat
    match map
        (k, a, pad) :: rest -> if k <= p then position_from rest p (a + sub (p - k) pad) else best
        []                  -> best

# A label normalized as CommonMark matches them: without white space at
# either end, each run of it a single space, and case folded.
export fn label_key label -> r : label~String, r~String
    let b = string.bytes label
    let i = skip is_ascii_space b 0
    let j = trim_end is_ascii_space b (len b) i
    string.fold_case (text_of (joined (collapse b i j False [])))

fn collapse b i j space acc -> r : b~Bytes, i~Nat, j~Nat, space~Bool, acc~List Bytes, r~List Bytes
    decreasing sub (len b) i
    if i < j and i < len b
        if b[i] == 32 or b[i] == 9 or b[i] == 10 or b[i] == 13
            collapse b (i + 1) j True acc
        else
            let acc2 = if space then b" " :: acc else acc
            collapse b (i + 1) j False (part b i (i + 1) :: acc2)
    else
        acc

# ── Inlines ──────────────────────────────────────────────────────────────────
# A paragraph's or heading's text becomes tokens, left to right: finished
# inlines, plain text, and runs of `*` or `_` that may open or close
# emphasis. A `]` that closes a link makes the tokens since its `[` the
# link's text; at the end, the delimiter runs left are matched up into
# emphasis (the spec's "process emphasis").

# A run of `*` or `_`: how many are left of it, how many it had, whether it
# can open or close emphasis, and where what is left starts.
record Delim
    ch~Nat
    count~Nat
    orig~Nat
    can_open~Bool
    can_close~Bool
    start~Nat

enum Tok
    TText text start stop : text~Bytes, start~Nat, stop~Nat
    TInline inline        : inline~Inline
    TDelim d              : d~Delim

# A `[` or `![` not yet closed: its token's number (from the first),
# whether it is an image's, whether it can still start a link, whether
# another came after it, where its `[` is, and where it starts.
record Bracket
    tok~Nat
    image~Bool
    active~Bool
    after~Bool
    index~Nat
    start~Nat

# What the inline parser has so far: its tokens (last first) and how many,
# the brackets not yet closed (last first), and the references that
# matched nothing (last first).
record IP
    toks~List Tok
    n~Nat
    brackets~List Bracket
    unresolved~List Reference

# What the inline parser reads: its text, where that text's bytes are in
# the source, the definitions (in order), and what resolves a reference
# none of them matches.
record Cx
    b~Bytes
    map~List (Nat, Nat, Nat)
    defs~List (Def, Span)
    resolve~(String -> Option Target)

fn span cx i j -> r : cx~Cx, i~Nat, j~Nat, r~Span
    Span (position cx.map i) (position cx.map j)

fn push ip t -> r : ip~IP, t~Tok, r~IP
    IP (t :: ip.toks) (ip.n + 1) ip.brackets ip.unresolved

fn push_text cx ip i j -> r : cx~Cx, ip~IP, i~Nat, j~Nat, r~IP
    push ip (TText (part cx.b i j) i j)

fn text_token cx ip text i j -> r : cx~Cx, ip~IP, text~Bytes, i~Nat, j~Nat, r~IP
    push ip (TText text i j)

fn inline_token cx ip x -> r : cx~Cx, ip~IP, x~Inline, r~IP
    push ip (TInline x)

# A byte with a meaning in inlines: it ends a run of plain text.
fn special c : c~Nat
    c == 10 or c == 96 or c == 91 or c == 93 or c == 92 or c == 33 or c == 60 or c == 38 or c == 42 or c == 95

# Read the inlines from `i`.
fn read_inlines cx ip i -> r : cx~Cx, ip~IP, i~Nat, r~IP
    decreasing sub (len cx.b) i
    if i < len cx.b
        match step cx ip i
            (ip2, j) -> if j > i then read_inlines cx ip2 j else read_inlines cx ip2 (i + 1)
    else
        ip

# One inline at `i`: the parser's state after it, and where it ends.
fn step cx ip i -> r : cx~Cx, ip~IP, i~Nat, r~(IP, Nat)
    let b = cx.b
    let c = at b i
    if c == 10
        newline cx ip i
    else if c == 92
        let d = at b (i + 1)
        if d == 10
            (inline_token cx ip (HardBreak (span cx i (i + 2))), skip_byte 32 b (i + 2))
        else if is_escapable d
            (push_text cx ip (i + 1) (i + 2), i + 2)
        else
            (push_text cx ip i (i + 1), i + 1)
    else if c == 96
        backticks cx ip i
    else if c == 42 or c == 95
        delims cx ip i c
    else if c == 91
        (open_bracket ip (push_text cx ip i (i + 1)) False i i, i + 1)
    else if c == 33 and at b (i + 1) == 91
        (open_bracket ip (push_text cx ip i (i + 2)) True (i + 1) i, i + 2)
    else if c == 93
        close_bracket cx ip i
    else if c == 60
        match autolink cx i
            Some (x, j) -> (inline_token cx ip x, j)
            None        ->
                match html_tag b i
                    Some j -> (inline_token cx ip (RawHtml (text_of (part b i j)) (span cx i j)), j)
                    None   -> (push_text cx ip i (i + 1), i + 1)
    else if c == 38
        match entity_at b i
            Some (s, j) -> (text_token cx ip s i j, j)
            None        -> (push_text cx ip i (i + 1), i + 1)
    else
        let j = skip (\x -> not (special x)) b (i + 1)
        (push_text cx ip i j, j)

# A line ending: a hard break after two or more spaces, else a soft one;
# the spaces around it are dropped.
fn newline cx ip i -> r : cx~Cx, ip~IP, i~Nat, r~(IP, Nat)
    let next = skip_byte 32 cx.b (i + 1)
    match ip.toks
        TText t s e :: rest ->
            let kept = trim_end (\x -> x == 32) t (len t) 0
            let spaces = sub (len t) kept
            if spaces > 0
                let ip2 = IP (TText (part t 0 kept) s (sub e spaces) :: rest) ip.n ip.brackets ip.unresolved
                let brk = if spaces >= 2 then HardBreak (span cx (sub i spaces) (i + 1)) else SoftBreak (span cx i (i + 1))
                (inline_token cx ip2 brk, next)
            else
                (inline_token cx ip (SoftBreak (span cx i (i + 1))), next)
        _                   -> (inline_token cx ip (SoftBreak (span cx i (i + 1))), next)

# A code span, or the backticks as text if no run of as many closes it.
fn backticks cx ip i -> r : cx~Cx, ip~IP, i~Nat, r~(IP, Nat)
    let b = cx.b
    let e = skip_byte 96 b i
    let n = sub e i
    match closing_ticks b e n
        Some k ->
            let content = spaces_for_newlines (part b e k)
            let all_spaces = skip_byte 32 content 0 >= len content
            let strip = len content >= 2 and at content 0 == 32 and at content (len content - 1) == 32 and not all_spaces
            let text = if strip then part content 1 (len content - 1) else content
            (inline_token cx ip (CodeSpan (text_of text) (span cx i (k + n))), k + n)
        None   -> (push_text cx ip i e, e)

# Where the next run of exactly `n` backticks from `i` starts.
fn closing_ticks b i n -> r : b~Bytes, i~Nat, n~Nat, r~Option Nat
    if i < len b
        if b[i] == 96
            let e = skip_byte 96 b i
            if e - i == n then Some i else closing_ticks b e n
        else
            closing_ticks b (i + 1) n
    else
        None

fn spaces_for_newlines b -> r : b~Bytes, r~Bytes
    match find b b"\n" 0
        None   -> b
        Some _ -> array.map (\c -> if c == 10 then 32 else c) b

# A run of `*` or `_`: whether it can open or close emphasis depends on
# what is on either side (the spec's left- and right-flanking runs).
fn delims cx ip i c -> r : cx~Cx, ip~IP, i~Nat, c~Nat, r~(IP, Nat)
    let b = cx.b
    let e = skip_byte c b i
    let n = sub e i
    let before = if i == 0 then c'\n' else or_newline (char_at b (char_before b i))
    let after = or_newline (char_at b e)
    let after_space = is_unicode_space after
    let after_punct = char.is_punctuation after
    let before_space = is_unicode_space before
    let before_punct = char.is_punctuation before
    let left = not after_space and (not after_punct or before_space or before_punct)
    let right = not before_space and (not before_punct or after_space or after_punct)
    let can_open = if c == 95 then left and (not right or before_punct) else left
    let can_close = if c == 95 then right and (not left or after_punct) else right
    if can_open or can_close
        (push ip (TDelim (Delim c n n can_open can_close i)), e)
    else
        (push_text cx ip i e, e)

fn or_newline c -> r : c~Option Char, r~Char
    match c
        Some x -> x
        None   -> c'\n'

fn open_bracket before ip image index start -> r : before~IP, ip~IP, image~Bool, index~Nat, start~Nat, r~IP
    let older = match ip.brackets
        b :: rest -> Bracket b.tok b.image b.active True b.index b.start :: rest
        []        -> []
    IP ip.toks ip.n (Bracket before.n image True False index start :: older) ip.unresolved

fn pop_bracket ip -> r : ip~IP, r~IP
    match ip.brackets
        _ :: rest -> IP ip.toks ip.n rest ip.unresolved
        []        -> ip

# A `]`: a link or an image if the last `[` can start one and a destination
# or a reference follows; else text.
fn close_bracket cx ip i -> r : cx~Cx, ip~IP, i~Nat, r~(IP, Nat)
    let b = cx.b
    let j = i + 1
    match ip.brackets
        []      -> (push_text cx ip i j, j)
        br :: _ ->
            if not br.active
                (push_text cx (pop_bracket ip) i j, j)
            else
                match inline_link b j
                    Some (t, e) -> (make_link cx ip br t None e, e)
                    None        ->
                        let label = link_label b j
                        let full = match label
                            Some e -> if e > j + 2 then Some (part b (j + 1) (e - 1), e) else None
                            None   -> None
                        let found = match full
                            Some (l, e) -> Some (l, e)
                            None        ->
                                if br.after
                                    None
                                else
                                    let e = match label
                                        Some e -> e
                                        None   -> j
                                    Some (part b (br.index + 1) i, e)
                        match found
                            Some (l, e) ->
                                match lookup cx l
                                    Some t -> (make_link cx ip br t (Some (text_of l)) e, e)
                                    None   ->
                                        let ip2 = unresolved cx ip l br.start e
                                        (push_text cx (pop_bracket ip2) i j, j)
                            None        -> (push_text cx (pop_bracket ip) i j, j)

# The definition or resolved reference label `l` names.
fn lookup cx l -> r : cx~Cx, l~Bytes, r~Option Target
    let key = label_key (text_of l)
    if key == "" or char_count l 0 0 > 999
        None
    else
        match find_def key cx.defs
            Some d -> Some (Target (text_of d.url) (title_text d.title))
            None   -> cx.resolve (text_of l)

fn title_text t -> r : t~Option Bytes, r~Option String
    match t
        Some x -> Some (text_of x)
        None   -> None

fn find_def key defs -> r : key~String, defs~List (Def, Span), r~Option Def
    match defs
        (d, _) :: rest -> if d.key == key then Some d else find_def key rest
        []             -> None

fn char_count b i n -> r : b~Bytes, i~Nat, n~Nat, r~Nat
    decreasing sub (len b) i
    if i < len b then char_count b (i + 1) (n + counts b[i]) else n

# Record a reference that matched nothing (if its label could match).
fn unresolved cx ip l start stop -> r : cx~Cx, ip~IP, l~Bytes, start~Nat, stop~Nat, r~IP
    if label_key (text_of l) == "" or char_count l 0 0 > 999
        ip
    else
        IP ip.toks ip.n ip.brackets (Reference (text_of l) (span cx start stop) :: ip.unresolved)

# `(destination "title")` at `j`: the target and where it ends.
fn inline_link b j -> r : b~Bytes, j~Nat, r~Option (Target, Nat)
    if at b j != 40
        None
    else
        match destination b (spnl b (j + 1))
            Some (url, d) ->
                let k = spnl b d
                let titled = if k > 0 and is_ascii_space (at b (k - 1)) then title b k else None
                let (t, e) = match titled
                    Some (tt, e) -> (Some (text_of tt), e)
                    None         -> (None, k)
                let close = spnl b e
                if at b close == 41 then Some (Target (text_of url) t, close + 1) else None
            None          -> None

# The link or image the bracket `br` starts: its text is the tokens after
# the bracket's; earlier brackets can't start links in a link.
fn make_link cx ip br t ref e -> r : cx~Cx, ip~IP, br~Bracket, t~Target, ref~Option String, e~Nat, r~IP
    let inner = list.take (sub ip.n (br.tok + 1)) ip.toks
    let before = list.drop (sub ip.n br.tok) ip.toks
    let content = emphasis cx (list.reverse inner)
    let s = span cx br.start e
    let x = if br.image then Image t content ref s else Link t content ref s
    let rest = match ip.brackets
        _ :: older -> if br.image then older else list.map deactivate older
        []         -> []
    IP (TInline x :: before) (br.tok + 1) rest ip.unresolved

fn deactivate br -> r : br~Bracket, r~Bracket
    if br.image then br else Bracket br.tok br.image False br.after br.index br.start

# An autolink at `i`: `<scheme:…>` or `<address@domain>`.
fn autolink cx i -> r : cx~Cx, i~Nat, r~Option (Inline, Nat)
    let b = cx.b
    match email b (i + 1)
        Some e if at b e == 62 ->
            let dest = decode_entities (part b (i + 1) e)
            let url = encode_url (bytes.concat [b"mailto:", dest])
            Some (Link (Target (text_of url) None) [Text (text_of dest) (span cx (i + 1) e)] None (span cx i (e + 1)), e + 1)
        _ ->
            let s = skip is_scheme_char b (i + 1)
            let n = sub s (i + 1)
            if is_letter (at b (i + 1)) and n >= 2 and n <= 32 and at b s == 58
                let e = skip (\c -> c > 32 and c != 60 and c != 62 and c != 256) b (s + 1)
                if at b e == 62
                    let dest = decode_entities (part b (i + 1) e)
                    Some (Link (Target (text_of (encode_url dest)) None) [Text (text_of dest) (span cx (i + 1) e)] None
                          (span cx i (e + 1)), e + 1)
                else
                    None
            else
                None

fn is_scheme_char c : c~Nat
    is_alnum c or c == 46 or c == 43 or c == 45

# An email address at `i`: where it ends.
fn email b i -> r : b~Bytes, i~Nat, r~Option Nat
    let at_sign = skip is_email_char b i
    if at_sign > i and at b at_sign == 64 then domain b (at_sign + 1) (len b) else None

fn is_email_char c : c~Nat
    is_alnum c or c == '.' or c == '!' or c == '#' or c == '$' or c == '%' or c == '&' or c == '\'' or c == '*'
        or c == '+' or c == '/' or c == '=' or c == '?' or c == '^' or c == '_' or c == '`' or c == '{'
        or c == '|' or c == '}' or c == '~' or c == '-'

# Labels of letters, digits and inner hyphens, at most 63 long, separated by
# dots.
fn domain b i fuel -> r : b~Bytes, i~Nat, fuel~Nat, r~Option Nat
    decreasing fuel
    let e = skip (\c -> is_alnum c or c == 45) b i
    let n = sub e i
    if n == 0 or n > 63 or at b i == 45 or at b (sub e 1) == 45
        None
    else if at b e == 46 and fuel > 0 and is_alnum (at b (e + 1))
        domain b (e + 1) (fuel - 1)
    else
        Some e

# `b` with its character references replaced (and not its backslashes).
fn decode_entities b -> r : b~Bytes, r~Bytes
    joined (decode_from b 0 0 [])

fn decode_from b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    decreasing sub (len b) i
    if i < len b
        if b[i] == 38
            match entity_at b i
                Some (s, stop) if stop > i -> decode_from b stop stop (s :: part b start i :: acc)
                _ -> decode_from b start (i + 1) acc
        else
            decode_from b start (i + 1) acc
    else
        part b start (len b) :: acc

# ── Emphasis ─────────────────────────────────────────────────────────────────

# Tokens as inlines, their runs of `*` and `_` matched up into emphasis:
# each run that can close, left to right, with the nearest run before it
# that can open it.
fn emphasis cx toks -> r : cx~Cx, toks~List Tok, r~List Inline
    let fuel = list.length toks + delim_total toks + 1
    as_inlines cx (list.reverse (match_runs cx [] toks fuel))

fn delim_total toks -> r : toks~List Tok, r~Nat
    match toks
        TDelim d :: rest -> d.count + delim_total rest
        _ :: rest        -> delim_total rest
        []               -> 0

# `left`: the tokens done (last first); `right`: the ones still to look at.
fn match_runs cx left right fuel -> r : cx~Cx, left~List Tok, right~List Tok, fuel~Nat, r~List Tok
    decreasing fuel
    match right
        []        -> left
        t :: rest ->
            if fuel == 0
                list.reverse right ++ left
            else
                match t
                    TDelim d if d.can_close ->
                        match opener left d 0
                            Some (k, o) ->
                                let use = if d.count >= 2 and o.count >= 2 then 2 else 1
                                let inner = list.reverse (list.take k left)
                                let before = list.drop (k + 1) left
                                let s = span cx (o.start + sub o.count use) (d.start + use)
                                let content = as_inlines cx inner
                                let x = if use == 1 then Emph content s else Strong content s
                                let o2 = Delim o.ch (sub o.count use) o.orig o.can_open o.can_close o.start
                                let d2 = Delim d.ch (sub d.count use) d.orig d.can_open d.can_close (d.start + use)
                                let left2 = TInline x :: (if o2.count > 0 then TDelim o2 :: before else before)
                                if d2.count > 0
                                    match_runs cx left2 (TDelim d2 :: rest) (fuel - 1)
                                else
                                    match_runs cx left2 rest (fuel - 1)
                            None        ->
                                if d.can_open
                                    match_runs cx (t :: left) rest (fuel - 1)
                                else
                                    match_runs cx (delim_text d :: left) rest (fuel - 1)
                    _ -> match_runs cx (t :: left) rest (fuel - 1)

# The nearest run in `left` (last first) that can open emphasis closed by
# `d`: how many tokens come after it, and the run.
fn opener left d k -> r : left~List Tok, d~Delim, k~Nat, r~Option (Nat, Delim)
    match left
        TDelim o :: rest ->
            let odd = (d.can_open or o.can_close) and d.orig % 3 != 0 and (o.orig + d.orig) % 3 == 0
            if o.ch == d.ch and o.can_open and not odd then Some (k, o) else opener rest d (k + 1)
        _ :: rest        -> opener rest d (k + 1)
        []               -> None

fn delim_text d -> r : d~Delim, r~Tok
    TText (run_of d) d.start (d.start + d.count)

fn run_of d -> r : d~Delim, r~Bytes
    array.repeat d.count (if d.ch == 42 then '*' else '_')

# Tokens as inlines; runs left over are text, and text next to text is one.
fn as_inlines cx toks -> r : cx~Cx, toks~List Tok, r~List Inline
    merge_text (list.map (as_inline cx) toks)

fn as_inline cx t -> r : cx~Cx, t~Tok, r~Inline
    match t
        TText s i j -> Text (text_of s) (span cx i j)
        TInline x   -> x
        TDelim d    -> Text (text_of (run_of d)) (span cx d.start (d.start + d.count))

fn merge_text xs -> r : xs~List Inline, r~List Inline
    match xs
        Text a sa :: Text b sb :: rest -> merge_text (Text (a ++ b) (Span sa.start sb.stop) :: rest)
        x :: rest                      -> x :: merge_text rest
        []                             -> []

# ── From raw blocks to blocks ────────────────────────────────────────────────

# The inlines of a paragraph's or heading's text (without white space at
# either end), and the references in it that matched nothing, onto `acc`.
fn parse_inlines defs resolve segs acc -> r : defs~List (Def, Span), resolve~(String -> Option Target),
                                              segs~List Seg, acc~List Reference, r~(List Inline, List Reference)
    let content = bytes.concat (list.map (\g -> g.text) segs)
    let i = skip is_ascii_space content 0
    let j = trim_end is_ascii_space content (len content) i
    let map = list.map (\(k, a, pad) -> (sub k i, a, pad)) (shift (seg_map segs) i)
    let cx = Cx (part content i j) map defs resolve
    let ip = read_inlines cx (IP [] 0 [] acc) 0
    (emphasis cx (list.reverse ip.toks), ip.unresolved)

# The map, for text that starts `i` bytes later: segments wholly before it
# start at it.
fn shift map i -> r : map~List (Nat, Nat, Nat), i~Nat, r~List (Nat, Nat, Nat)
    match map
        (k, a, pad) :: rest -> (if k < i then (i, a + sub (i - k) pad, 0) else (k, a, pad)) :: shift rest i
        []                  -> []

fn span_of w -> r : w~Where, r~Span
    Span w.start w.stop

fn blocks_of defs resolve raws acc -> r : defs~List (Def, Span), resolve~(String -> Option Target), raws~List Raw,
                                          acc~List Reference, r~(List Block, List Reference)
    match raws
        []        -> ([], acc)
        x :: rest ->
            match block_of defs resolve x acc
                (b, acc2) -> match blocks_of defs resolve rest acc2
                    (bs, acc3) -> (b :: bs, acc3)

fn block_of defs resolve x acc -> r : defs~List (Def, Span), resolve~(String -> Option Target), x~Raw,
                                      acc~List Reference, r~(Block, List Reference)
    match x
        RPara segs w          ->
            match parse_inlines defs resolve segs acc
                (xs, acc2) -> (Paragraph xs (span_of w), acc2)
        RHeading level segs w ->
            match parse_inlines defs resolve segs acc
                (xs, acc2) -> (Heading level xs (span_of w), acc2)
        RBreak w              -> (ThematicBreak (span_of w), acc)
        RQuote cs w           ->
            match blocks_of defs resolve cs acc
                (bs, acc2) -> (Quote bs (span_of w), acc2)
        RList d t items w     ->
            match items_of defs resolve items acc
                (is, acc2) -> (if d.ordered then Numbered d.start t is (span_of w) else Bullets t is (span_of w), acc2)
        RItem cs w            ->
            match blocks_of defs resolve cs acc
                (bs, acc2) -> (Quote bs (span_of w), acc2)
        RCode _ info segs w   ->
            let lines = list.map (\g -> Span g.at (g.at + sub (len g.text) (g.pad + 1))) segs
            (Code (text_of info) (text_of (bytes.concat (list.map (\g -> g.text) segs))) lines (span_of w), acc)
        RHtml segs w          -> (Html (text_of (without_newline (bytes.concat (list.map (\g -> g.text) segs)))) (span_of w), acc)

fn items_of defs resolve raws acc -> r : defs~List (Def, Span), resolve~(String -> Option Target), raws~List Raw,
                                         acc~List Reference, r~(List Item, List Reference)
    match raws
        RItem cs w :: rest ->
            match blocks_of defs resolve cs acc
                (bs, acc2) -> match items_of defs resolve rest acc2
                    (is, acc3) -> (Item bs (span_of w) :: is, acc3)
        _ :: rest          -> items_of defs resolve rest acc
        []                 -> ([], acc)

# ── Parsing ──────────────────────────────────────────────────────────────────

# The document `text` is, as CommonMark parses it.
export fn parse text -> d : text~String, d~Document
    parse_with (\_ -> None) text

# The document `text` is, where `resolve` is asked about each reference
# (`[label]`, `[text][label]`, `[label][]`) that no definition matches, with
# its label as written: a target it gives makes the reference a link.
export fn parse_with resolve text -> d : resolve~(String -> Option Target), text~String, d~Document
    let src = string.bytes text
    match strip_definitions (raw_blocks src) []
        (raws, found) ->
            let defs = list.reverse found
            match blocks_of defs resolve raws []
                (bs, refs) -> Document bs (list.map definition defs) (list.reverse refs)

fn definition ds -> r : ds~(Def, Span), r~Definition
    match ds
        (d, s) -> Definition (text_of d.label) (Target (text_of d.url) (title_text d.title)) s

# ── Helpers ──────────────────────────────────────────────────────────────────

# An info string's first word: a code block's language (`checkers` in
# "checkers,no_run").
export fn language info -> r : info~String, r~String
    let b = string.bytes info
    let i = skip is_ascii_space b 0
    text_of (part b i (skip (\c -> not (is_ascii_space c)) b i))

# The text of inlines, without their markup: an image's `alt`.
export fn plain xs -> r : xs~List Inline, r~String
    match xs
        x :: rest -> plain_one x ++ plain rest
        []        -> ""

fn plain_one x -> r : x~Inline, r~String
    match x
        Text s _       -> s
        CodeSpan s _   -> s
        Emph xs _      -> plain xs
        Strong xs _    -> plain xs
        Link _ xs _ _  -> plain xs
        Image _ xs _ _ -> plain xs
        RawHtml _ _    -> ""
        SoftBreak _    -> "\n"
        HardBreak _    -> "\n"

# ── HTML ─────────────────────────────────────────────────────────────────────
# As commonmark.js renders it: a line break before and after each block,
# but never two in a row.

# What has been written (last first), and whether the last thing written
# was a single line break.
record R
    out~List Bytes
    nl~Bool

fn lit r s -> q : r~R, s~Bytes, q~R
    R (s :: r.out) (s == b"\n")

fn cr r -> q : r~R, q~R
    if r.nl then r else lit r b"\n"

fn esc s -> r : s~String, r~Bytes
    string.bytes (html.escape s)

# The document as HTML.
export fn to_html d -> r : d~Document, r~String
    to_html_with (\_ _ -> None) d

# The document as HTML, where `code info text` may give a code block's HTML
# instead of `<pre><code>…</code></pre>`.
export fn to_html_with code d -> r : code~(String -> String -> Option String), d~Document, r~String
    text_of (joined (render_blocks code False d.blocks (R [] True)).out)

fn render_blocks code tight bs r -> q : code~(String -> String -> Option String), tight~Bool, bs~List Block, r~R, q~R
    match bs
        b :: rest -> render_blocks code tight rest (render_block code tight b r)
        []        -> r

fn render_block code tight b r -> q : code~(String -> String -> Option String), tight~Bool, b~Block, r~R, q~R
    match b
        Paragraph xs _           ->
            if tight then render_inlines xs False r else cr (lit (render_inlines xs False (lit (cr r) b"<p>")) b"</p>")
        Heading level xs _       ->
            let n = decimal level
            cr (lit (render_inlines xs False (lit (cr r) (bytes.concat [b"<h", n, b">"]))) (bytes.concat [b"</h", n, b">"]))
        ThematicBreak _          -> cr (lit (cr r) b"<hr />")
        Quote bs _               ->
            cr (lit (cr (render_blocks code False bs (cr (lit (cr r) b"<blockquote>")))) b"</blockquote>")
        Bullets t items _        ->
            cr (lit (cr (render_items code t items (cr (lit (cr r) b"<ul>")))) b"</ul>")
        Numbered start t items _ ->
            let open = if start == 1 then b"<ol>" else bytes.concat [b"<ol start=\"", decimal start, b"\">"]
            cr (lit (cr (render_items code t items (cr (lit (cr r) open)))) b"</ol>")
        Code info text _ _       ->
            match code info text
                Some h -> cr (lit (cr r) (string.bytes h))
                None   ->
                    let word = string.bytes (language info)
                    let cls = if len word == 0
                        b""
                    else if bytes.matches_at word 0 b"language-"
                        bytes.concat [b" class=\"", esc (text_of word), b"\""]
                    else
                        bytes.concat [b" class=\"language-", esc (text_of word), b"\""]
                    cr (lit (cr r) (bytes.concat [b"<pre><code", cls, b">", esc text, b"</code></pre>"]))
        Html text _              -> cr (lit (cr r) (string.bytes text))

fn render_items code tight items r -> q : code~(String -> String -> Option String), tight~Bool, items~List Item, r~R, q~R
    match items
        Item bs _ :: rest -> render_items code tight rest (cr (lit (render_blocks code tight bs (lit r b"<li>")) b"</li>"))
        []                -> r

# Inlines as HTML; in an image's `alt` (`alt`), only their text.
fn render_inlines xs alt r -> q : xs~List Inline, alt~Bool, r~R, q~R
    match xs
        x :: rest -> render_inlines rest alt (render_inline x alt r)
        []        -> r

fn tag r alt s -> q : r~R, alt~Bool, s~Bytes, q~R
    if alt then r else lit r s

fn render_inline x alt r -> q : x~Inline, alt~Bool, r~R, q~R
    match x
        Text s _       -> lit r (esc s)
        SoftBreak _    -> lit r b"\n"
        HardBreak _    -> cr (tag r alt b"<br />")
        CodeSpan s _   -> tag (lit (tag r alt b"<code>") (esc s)) alt b"</code>"
        Emph xs _      -> tag (render_inlines xs alt (tag r alt b"<em>")) alt b"</em>"
        Strong xs _    -> tag (render_inlines xs alt (tag r alt b"<strong>")) alt b"</strong>"
        RawHtml s _    -> if alt then r else lit r (string.bytes s)
        Link t xs _ _  ->
            let open = bytes.concat [b"<a href=\"", esc t.url, b"\"", title_attr t, b">"]
            tag (render_inlines xs alt (tag r alt open)) alt b"</a>"
        Image t xs _ _ ->
            if alt
                render_inlines xs True r
            else
                let r2 = render_inlines xs True (lit r (bytes.concat [b"<img src=\"", esc t.url, b"\" alt=\""]))
                lit r2 (bytes.concat [b"\"", title_attr t, b" />"])

fn title_attr t -> r : t~Target, r~Bytes
    match t.title
        Some s -> if s == "" then b"" else bytes.concat [b" title=\"", esc s, b"\""]
        None   -> b""
