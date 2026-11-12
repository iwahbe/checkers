# ck/markdown.ck — Markdown to HTML, for the documentation and the site
# (SPEC §15.6, D131). A subset: headings, paragraphs, bullet and numbered
# lists, block quotes, fenced code, tables, links, emphasis, strong text and
# inline code. Anything else is shown as text. Links to `.md` pages become
# links to `.html` pages, and `checkers` code blocks are highlighted.

module ck.markdown

import std.bytes
import std.string
import std.list
import ck.syntax (Tok, Line, Name, Upper, Number, Literal, Punct, Comment)
import ck.syntax

# ── Bytes ────────────────────────────────────────────────────────────────────

fn at b i -> r : b~Bytes, i~Nat, r~U8
    if i < len b then b[i] else 0

fn starts b prefix : b~Bytes, prefix~Bytes
    bytes.matches_at b 0 prefix

fn from b i -> r : b~Bytes, i~Nat, r~Bytes
    if i <= len b then bytes.slice b i (len b) else b""

fn part b i j -> r : b~Bytes, i~Nat, j~Nat, r~Bytes
    if i <= j and j <= len b then bytes.slice b i j else b""

fn is_space c : c~U8
    c == ' ' or c == '\t'

partial fn lead b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b and is_space b[i] then lead b (i + 1) else i

partial fn tail_end b j -> r : b~Bytes, j~Nat, r~Nat
    if j > 0 and j <= len b and is_space b[j - 1] then tail_end b (j - 1) else j

# Without spaces at either end.
partial fn trim b -> r : b~Bytes, r~Bytes
    let i = lead b 0
    let j = tail_end b (len b)
    if i <= j then part b i j else b""

export partial fn blank b : b~Bytes
    lead b 0 == len b

# The text's lines, without their line breaks.
export partial fn lines_of b -> r : b~Bytes, r~List Bytes
    list.reverse (split_lines b 0 0 [])

partial fn split_lines b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    if i >= len b
        if start < len b then without_cr (part b start (len b)) :: acc else acc
    else if b[i] == '\n'
        split_lines b (i + 1) (i + 1) (without_cr (part b start i) :: acc)
    else
        split_lines b start (i + 1) acc

fn without_cr b -> r : b~Bytes, r~Bytes
    if len b > 0 and b[len b - 1] == '\r' then bytes.slice b 0 (len b - 1) else b

# ── Escaping ─────────────────────────────────────────────────────────────────

# `&`, `<`, `>` and `"` as entities.
export partial fn escape b -> r : b~Bytes, r~Bytes
    bytes.concat (list.reverse (escape_from b 0 0 []))

partial fn escape_from b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    if i >= len b
        part b start (len b) :: acc
    else
        let entity = entity_of b[i]
        if len entity > 0
            escape_from b (i + 1) (i + 1) (entity :: part b start i :: acc)
        else
            escape_from b start (i + 1) acc

fn entity_of c -> r : c~U8, r~Bytes
    if c == '&'
        b"&amp;"
    else if c == '<'
        b"&lt;"
    else if c == '>'
        b"&gt;"
    else if c == '"'
        b"&quot;"
    else
        b""

# ── Inline text ──────────────────────────────────────────────────────────────

# The position of `word` in `b` at or after `i`.
partial fn find b word i -> r : b~Bytes, word~Bytes, i~Nat, r~Option Nat
    if i + len word > len b
        None
    else if bytes.matches_at b i word
        Some i
    else
        find b word (i + 1)

# A link's target as HTML wants it: a relative link to a `.md` page goes to
# its `.html` twin.
partial fn target url -> r : url~Bytes, r~Bytes
    let external = find url b"://" 0 != None or starts url b"mailto:" or starts url b"#"
    if external
        url
    else
        let hash = match find url b"#" 0
            Some k -> k
            None   -> len url
        let path = part url 0 hash
        if len path >= 3 and bytes.matches_at path (len path - 3) b".md"
            bytes.concat [part path 0 (len path - 3), b".html", from url hash]
        else
            url

fn punct c : c~U8
    c == '\\' or c == '`' or c == '*' or c == '_' or c == '[' or c == ']' or c == '(' or c == ')' or c == '#'
        or c == '|' or c == '<' or c == '>' or c == '!' or c == '-' or c == '.'

# Inline Markdown as HTML.
export partial fn inline b -> r : b~Bytes, r~Bytes
    bytes.concat (list.reverse (inline_from b 0 0 []))

# `start` is where the text not yet written begins.
partial fn inline_from b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    if i >= len b
        escape (part b start (len b)) :: acc
    else
        let c = b[i]
        let before = escape (part b start i) :: acc
        if c == '\\' and i + 1 < len b and punct (at b (i + 1))
            inline_from b (i + 2) (i + 2) (escape (part b (i + 1) (i + 2)) :: before)
        else if c == '`'
            match find b b"`" (i + 1)
                Some k ->
                    let code = bytes.concat [b"<code>", escape (part b (i + 1) k), b"</code>"]
                    inline_from b (k + 1) (k + 1) (code :: before)
                None   -> inline_from b start (i + 1) acc
        else if c == '*' and at b (i + 1) == '*'
            match find b b"**" (i + 2)
                Some k if k > i + 2 ->
                    let s = bytes.concat [b"<strong>", inline (part b (i + 2) k), b"</strong>"]
                    inline_from b (k + 2) (k + 2) (s :: before)
                _ -> inline_from b start (i + 2) acc
        else if c == '*' and i + 1 < len b and not (is_space (at b (i + 1)))
            match find b b"*" (i + 1)
                Some k if k > i + 1 and not (is_space (at b (k -1))) ->
                    let s = bytes.concat [b"<em>", inline (part b (i + 1) k), b"</em>"]
                    inline_from b (k + 1) (k + 1) (s :: before)
                _ -> inline_from b start (i + 1) acc
        else if c == '['
            match link b i
                Some (text, url, k) ->
                    let a = bytes.concat [b"<a href=\"", escape (target url), b"\">", inline text, b"</a>"]
                    inline_from b k k (a :: before)
                None                -> inline_from b start (i + 1) acc
        else
            inline_from b start (i + 1) acc

# A link `[text](url)` at `i`: its text, its target, and where it ends.
partial fn link b i -> r : b~Bytes, i~Nat, r~Option (Bytes, Bytes, Nat)
    match close_bracket b (i + 1) 0
        Some k if at b (k + 1) == '(' ->
            match find b b")" (k + 2)
                Some e -> Some (part b (i + 1) k, part b (k + 2) e, e + 1)
                None   -> None
        _ -> None

# The `]` that closes a `[` before `i` (`depth` more are open), skipping code.
partial fn close_bracket b i depth -> r : b~Bytes, i~Nat, depth~Nat, r~Option Nat
    if i >= len b
        None
    else if b[i] == '`'
        match find b b"`" (i + 1)
            Some k -> close_bracket b (k + 1) depth
            None   -> None
    else if b[i] == '['
        close_bracket b (i + 1) (depth + 1)
    else if b[i] == ']'
        if depth == 0 then Some i else close_bracket b (i + 1) (depth - 1)
    else
        close_bracket b (i + 1) depth

# ── Code ─────────────────────────────────────────────────────────────────────

partial fn spaces n -> r : n~Nat, r~Bytes
    if n == 0 then b"" else bytes.concat [b" ", spaces (n - 1)]

fn class_of t -> r : t~Tok, r~Bytes
    match t.kind
        Name    -> if syntax.is_keyword t or syntax.is_binop t then b"kw" else b""
        Upper   -> b"ty"
        Number  -> b"nu"
        Literal -> b"st"
        Comment -> b"co"
        Punct   -> b""

partial fn span t -> r : t~Tok, r~Bytes
    let c = class_of t
    if len c == 0 then escape t.text else bytes.concat [b"<span class=\"", c, b"\">", escape t.text, b"</span>"]

# Where a highlighter is in a signature (§15.6): in a type (after `~`, until
# a `,` or `:` outside brackets), how deep in brackets, the name just before
# (for a qualifier), and the qualifier of the next name (`files` in
# `files.File`).
record Place
    ty~Bool
    depth~Nat
    last~Bytes
    qual~Bytes

let START = Place False 0 b"" b""

partial fn step t h -> r : t~Tok, h~Place, r~Place
    match t.kind
        Comment -> h
        Name    -> Place (h.ty and not (syntax.is_keyword t)) h.depth t.text b""
        Punct   ->
            if t.text == b"~"
                Place True 0 b"" b""
            else if t.text == b"(" or t.text == b"["
                Place h.ty (h.depth + 1) b"" b""
            else if t.text == b")" or t.text == b"]"
                Place h.ty (if h.depth > 0 then h.depth - 1 else 0) b"" b""
            else if (t.text == b"," or t.text == b":") and h.depth == 0
                START
            else if t.text == b"."
                Place h.ty h.depth b"" h.last
            else
                Place h.ty h.depth b"" b""
        _       -> Place h.ty h.depth b"" b""

# A token, a link if it is a name `links` knows: `links qualifier name ty`
# gives the address of a name's declaration, `ty` saying it is in a type.
partial fn linked t h links -> r : t~Tok, h~Place, links~(Bytes -> Bytes -> Bool -> Option Bytes), r~Bytes
    let s = span t
    match t.kind
        Upper ->
            match links h.qual t.text h.ty
                Some url -> bytes.concat [b"<a href=\"", escape url, b"\">", s, b"</a>"]
                None     -> s
        _     -> s

# One line's tokens, spaced as written (columns are in characters).
partial fn line_html toks col h links acc -> r : toks~List Tok, col~Nat, h~Place,
                                                 links~(Bytes -> Bytes -> Bool -> Option Bytes), acc~List Bytes,
                                                 r~(List Bytes, Place)
    match toks
        []        -> (acc, h)
        t :: rest ->
            let gap = if t.col >= col then t.col - col else 0
            line_html rest (t.col + t.wide) (step t h) links (linked t h links :: spaces gap :: acc)

# A new line outside brackets starts outside a type (the next field, say).
partial fn lines_html ls next h links acc -> r : ls~List Line, next~Nat, h~Place,
                                                 links~(Bytes -> Bytes -> Bool -> Option Bytes), acc~List Bytes,
                                                 r~List Bytes
    match ls
        []        -> acc
        l :: rest ->
            if l.num > next
                lines_html ls (next + 1) h links (b"\n" :: acc)
            else
                let toks = match l.comment
                    Some c -> l.toks ++ [c]
                    None   -> l.toks
                let fresh = if h.depth == 0 then START else h
                let (out, after) = line_html toks 0 fresh links acc
                lines_html rest (l.num + 1) after links (b"\n" :: out)

# A code block: highlighted if it is Checkers that lexes, else as written.
partial fn code lang body links -> r : lang~Bytes, body~List Bytes,
                                       links~(Bytes -> Bytes -> Bool -> Option Bytes), r~Bytes
    let text = bytes.concat (list.map (\l -> bytes.concat [l, b"\n"]) body)
    let inner = if lang == b"checkers"
        match syntax.lex text
            Ok ls -> bytes.concat (list.reverse (lines_html ls 1 START links []))
            Err _ -> escape text
    else
        escape text
    let cls = if len lang > 0 then bytes.concat [b" class=\"language-", escape lang, b"\""] else b""
    bytes.concat [b"<pre><code", cls, b">", inner, b"</code></pre>\n"]

# ── Blocks ───────────────────────────────────────────────────────────────────

partial fn heading_level b n -> r : b~Bytes, n~Nat, r~Nat
    if n < 6 and at b n == '#' then heading_level b (n + 1) else if n > 0 and at b n == ' ' then n else 0

# An anchor for a heading: its words in lower case, joined by `-`.
export partial fn slug b -> r : b~Bytes, r~Bytes
    bytes.concat (list.reverse (slug_from b 0 False []))

partial fn slug_from b i dash acc -> r : b~Bytes, i~Nat, dash~Bool, acc~List Bytes, r~List Bytes
    if i >= len b
        acc
    else
        let c = b[i]
        let lower = c >= 'A' and c <= 'Z'
        let keep = (c >= 'a' and c <= 'z') or (c >= '0' and c <= '9') or c == '_' or c >= 0x80
        if lower
            slug_from b (i + 1) False (one (c + 32) :: (if dash and acc != [] then [b"-"] else []) ++ acc)
        else if keep
            slug_from b (i + 1) False (part b i (i + 1) :: (if dash and acc != [] then [b"-"] else []) ++ acc)
        else
            slug_from b (i + 1) True acc

fn one c -> r : c~Nat, r~Bytes
    let table = b"0123456789abcdefghijklmnopqrstuvwxyz"
    if c >= 'a' and c <= 'z' then part table (c - 'a' + 10) (c - 'a' + 11) else b""

# A bullet item's text, if `b` starts one.
partial fn bullet b -> r : b~Bytes, r~Option Bytes
    let i = lead b 0
    if i <= 1 and (bytes.matches_at b i b"- " or bytes.matches_at b i b"* ")
        Some (from b (i + 2))
    else
        None

partial fn digits_end b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b and b[i] >= '0' and b[i] <= '9' then digits_end b (i + 1) else i

# A numbered item's text, if `b` starts one.
partial fn numbered b -> r : b~Bytes, r~Option Bytes
    let i = lead b 0
    let j = digits_end b i
    if i <= 1 and j > i and bytes.matches_at b j b". " then Some (from b (j + 2)) else None

fn fence b : b~Bytes
    starts b b"```"

partial fn quote b : b~Bytes
    starts b b">"

partial fn table_row b : b~Bytes
    starts (trim b) b"|"

partial fn separator b : b~Bytes
    let t = trim b
    starts t b"|" and only_rule t 0

partial fn only_rule b i : b~Bytes, i~Nat
    if i >= len b
        True
    else
        let c = b[i]
        (c == '|' or c == '-' or c == ':' or c == ' ') and only_rule b (i + 1)

# Whether `b` starts a block other than a paragraph.
partial fn opens b : b~Bytes
    fence b or heading_level b 0 > 0 or bullet b != None or numbered b != None or quote b or table_row b

# Markdown as HTML.
export partial fn to_html text -> r : text~Bytes, r~Bytes
    to_html_linked text (\q n ty -> None)

# Markdown as HTML, with the names in `checkers` code that `links` knows as
# links to their declarations (`links qualifier name ty`, see `linked`).
export partial fn to_html_linked text links -> r : text~Bytes, links~(Bytes -> Bytes -> Bool -> Option Bytes),
                                                   r~Bytes
    bytes.concat (list.reverse (blocks (lines_of text) links []))

partial fn blocks ls links acc -> r : ls~List Bytes, links~(Bytes -> Bytes -> Bool -> Option Bytes),
                                      acc~List Bytes, r~List Bytes
    match ls
        []        -> acc
        l :: rest ->
            let h = heading_level l 0
            let starts_table = match rest
                next :: _ -> table_row l and separator next
                []        -> False
            if blank l
                blocks rest links acc
            else if fence l
                let (body, after) = fenced rest []
                blocks after links (code (trim (from l 3)) body links :: acc)
            else if h > 0
                let text = trim (from l (h + 1))
                let n = string.bytes (format h)
                let html = bytes.concat [b"<h", n, b" id=\"", slug text, b"\">", inline text, b"</h", n, b">\n"]
                blocks rest links (html :: acc)
            else if starts_table
                let (rows, after) = take_rows (list.drop 1 rest) []
                blocks after links (table l rows :: acc)
            else if bullet l != None
                let (items, after) = items_of bullet rest (item_text bullet l) []
                blocks after links (list_html b"ul" items :: acc)
            else if numbered l != None
                let (items, after) = items_of numbered rest (item_text numbered l) []
                blocks after links (list_html b"ol" items :: acc)
            else if quote l
                let (inner, after) = quoted ls []
                blocks after links (bytes.concat [b"<blockquote>\n", to_html_linked (joined inner) links, b"</blockquote>\n"] :: acc)
            else
                let (para, after) = paragraph rest [l]
                blocks after links (bytes.concat [b"<p>", inline (joined para), b"</p>\n"] :: acc)

partial fn joined ls -> r : ls~List Bytes, r~Bytes
    match ls
        []        -> b""
        [x]       -> x
        x :: rest -> bytes.concat [x, b"\n", joined rest]

# The lines of a fenced block, and the lines after its closing fence.
partial fn fenced ls acc -> r : ls~List Bytes, acc~List Bytes, r~(List Bytes, List Bytes)
    match ls
        []        -> (list.reverse acc, [])
        l :: rest -> if fence (trim l) then (list.reverse acc, rest) else fenced rest (l :: acc)

partial fn paragraph ls acc -> r : ls~List Bytes, acc~List Bytes, r~(List Bytes, List Bytes)
    match ls
        []        -> (list.reverse acc, [])
        l :: rest -> if blank l or opens l then (list.reverse acc, ls) else paragraph rest (trim l :: acc)

partial fn quoted ls acc -> r : ls~List Bytes, acc~List Bytes, r~(List Bytes, List Bytes)
    match ls
        []        -> (list.reverse acc, [])
        l :: rest ->
            if quote l
                let t = from l 1
                quoted rest ((if starts t b" " then from t 1 else t) :: acc)
            else
                (list.reverse acc, ls)

partial fn item_text kind l -> r : kind~(Bytes -> Option Bytes), l~Bytes, r~List Bytes
    match kind l
        Some t -> [t]
        None   -> [l]

# A list's items (each its lines, the continuation lines unindented), and the
# lines after it. A blank line ends the list unless an item or an indented
# line follows.
partial fn items_of kind ls cur acc -> r : kind~(Bytes -> Option Bytes), ls~List Bytes, cur~List Bytes,
                                           acc~List (List Bytes), r~(List (List Bytes), List Bytes)
    let done = list.reverse (cur :: acc)
    match ls
        []        -> (done, [])
        l :: rest ->
            match kind l
                Some t -> items_of kind rest [t] (cur :: acc)
                None   ->
                    if blank l
                        match rest
                            next :: _ if kind next != None or (not (blank next) and lead next 0 >= 2) ->
                                items_of kind rest (cur ++ [b""]) acc
                            _ -> (done, rest)
                    else if lead l 0 >= 2
                        items_of kind rest (cur ++ [from l (min (lead l 0) 4)]) acc
                    else if opens l
                        (done, ls)
                    else
                        items_of kind rest (cur ++ [trim l]) acc

fn min a b -> r : a~Nat, b~Nat, r~Nat
    if a < b then a else b

partial fn list_html tag items -> r : tag~Bytes, items~List (List Bytes), r~Bytes
    let lis = list.map (\it -> bytes.concat [b"<li>", item_html it, b"</li>\n"]) items
    bytes.concat ([b"<", tag, b">\n"] ++ lis ++ [b"</", tag, b">\n"])

# An item of one paragraph is inline text; one with more is blocks.
partial fn item_html it -> r : it~List Bytes, r~Bytes
    if list.all (\l -> not (blank l) and not (opens l)) (list.drop 1 it)
        inline (joined it)
    else
        to_html (joined it)

partial fn take_rows ls acc -> r : ls~List Bytes, acc~List Bytes, r~(List Bytes, List Bytes)
    match ls
        []        -> (list.reverse acc, [])
        l :: rest -> if table_row l then take_rows rest (l :: acc) else (list.reverse acc, ls)

partial fn table head rows -> r : head~Bytes, rows~List Bytes, r~Bytes
    let th = row_html b"th" head
    let trs = list.map (\r -> row_html b"td" r) rows
    bytes.concat ([b"<table>\n<thead>\n", th, b"</thead>\n<tbody>\n"] ++ trs ++ [b"</tbody>\n</table>\n"])

partial fn row_html tag row -> r : tag~Bytes, row~Bytes, r~Bytes
    let cells = cells_of (trim row)
    let tds = list.map (\c -> bytes.concat [b"<", tag, b">", inline (unescape_pipes (trim c) 0 0 []), b"</", tag, b">"]) cells
    bytes.concat ([b"<tr>"] ++ tds ++ [b"</tr>\n"])

# A cell with each `\|` as `|`, inside code too: the escape belongs to the
# table (as on GitHub).
partial fn unescape_pipes b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~Bytes
    if i + 1 >= len b
        bytes.concat (list.reverse (part b start (len b) :: acc))
    else if b[i] == '\\' and b[i + 1] == '|'
        unescape_pipes b (i + 1) (i + 2) (part b start i :: acc)
    else
        unescape_pipes b start (i + 1) acc

# A row's cells: split at `|`, but not inside code or after `\`.
partial fn cells_of b -> r : b~Bytes, r~List Bytes
    let inner = if starts b b"|" then from b 1 else b
    let body = if len inner > 0 and inner[len inner - 1] == '|' then part inner 0 (len inner - 1) else inner
    list.reverse (cells_from body 0 0 False [])

partial fn cells_from b start i code acc -> r : b~Bytes, start~Nat, i~Nat, code~Bool, acc~List Bytes,
                                                r~List Bytes
    if i >= len b
        part b start (len b) :: acc
    else
        let c = b[i]
        if c == '\\' and i + 1 < len b
            cells_from b start (i + 2) code acc
        else if c == '`'
            cells_from b start (i + 1) (not code) acc
        else if c == '|' and not code
            cells_from b (i + 1) (i + 1) code (part b start i :: acc)
        else
            cells_from b start (i + 1) code acc

# The text of the first heading, if there is one.
export partial fn title text -> r : text~Bytes, r~Option Bytes
    first_heading (lines_of text)

partial fn first_heading ls -> r : ls~List Bytes, r~Option Bytes
    match ls
        []        -> None
        l :: rest ->
            let h = heading_level l 0
            if h > 0 then Some (trim (from l (h + 1))) else first_heading rest
