# ck/literate.ck — Markdown with Checkers in it, for the documentation and
# the site (D148, §15.6): pages parsed by `std.markdown`, `[name]` links to
# the documentation of the symbols they name, and code blocks compiled (and
# run, if they have `main`) by `ckc`, their output shown after them. What
# goes wrong is a warning (W030–W034) at its place on the page.
#
# CommonMark has no tables; a paragraph whose lines are all `| … |` rows,
# the second a rule (`|---|---|`), is shown as one, as on GitHub.

module ck.literate

import std.system (Proc)
import std.files (Fs)
import std.files
import std.proc
import std.json (Json, Arr, Str)
import std.markdown (Document, Block, Inline, Item, Span, Target, Definition, Reference, Paragraph, Heading,
                     ThematicBreak, Quote, Bullets, Numbered, Code, Html, Text, CodeSpan, Emph, Strong, Link, Image,
                     RawHtml, SoftBreak, HardBreak)
import std.markdown
import std.html
import std.string
import std.bytes
import std.list
import ck.syntax (Tok, Line, Name, Upper, Number, Literal, Punct, Comment)
import ck.syntax
import ck.jsonrpc as rpc
import ck.text (as_string)

# ── Bytes ────────────────────────────────────────────────────────────────────

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
export partial fn trim b -> r : b~Bytes, r~Bytes
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

# `&`, `<`, `>` and `"` as character references.
export fn escape b -> r : b~Bytes, r~Bytes
    string.bytes (html.escape (as_string b))

# The position of `word` in `b` at or after `i`.
partial fn find b word i -> r : b~Bytes, word~Bytes, i~Nat, r~Option Nat
    if i + len word > len b
        None
    else if bytes.matches_at b i word
        Some i
    else
        find b word (i + 1)

# The line (from 1) and column (from 1, in bytes) of `offset` in `text`.
export partial fn line_col text offset -> r : text~Bytes, offset~Nat, r~(Nat, Nat)
    line_col_from text offset 0 1 0

partial fn line_col_from text offset i line start -> r : text~Bytes, offset~Nat, i~Nat, line~Nat, start~Nat,
                                                         r~(Nat, Nat)
    if i >= offset or i >= len text
        (line, (if i >= start then i - start else 0) + 1)
    else if text[i] == '\n'
        line_col_from text offset (i + 1) (line + 1) (i + 1)
    else
        line_col_from text offset (i + 1) line start

# ── Headings ─────────────────────────────────────────────────────────────────

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

# The text of the first heading, as written (marks and all), if there is one.
export partial fn title text -> r : text~Bytes, r~Option Bytes
    first_heading text (markdown.parse (as_string text)).blocks

partial fn first_heading text bs -> r : text~Bytes, bs~List Block, r~Option Bytes
    match bs
        Heading _ _ s :: _ -> Some (heading_text (part text s.start s.stop))
        _ :: rest          -> first_heading text rest
        []                 -> None

# An ATX heading's line without its `#`s, or a setext heading's first line.
partial fn heading_text b -> r : b~Bytes, r~Bytes
    let line = match lines_of b
        l :: _ -> l
        []     -> b""
    let t = trim line
    let hashes = skip_hashes t 0
    let inner = trim (from t hashes)
    let e = skip_back_hashes inner (len inner)
    if hashes > 0 and e < len inner and (e == 0 or is_space inner[e - 1]) then trim (part inner 0 e) else inner

partial fn skip_hashes b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b and b[i] == '#' then skip_hashes b (i + 1) else i

partial fn skip_back_hashes b j -> r : b~Bytes, j~Nat, r~Nat
    if j > 0 and j <= len b and b[j - 1] == '#' then skip_back_hashes b (j - 1) else j

# ── Highlighting ─────────────────────────────────────────────────────────────

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

fn span t -> r : t~Tok, r~Bytes
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

fn step t h -> r : t~Tok, h~Place, r~Place
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
fn linked t h links -> r : t~Tok, h~Place, links~(Bytes -> Bytes -> Bool -> Option Bytes), r~Bytes
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

# Checkers code as HTML: highlighted if it lexes, else as written.
partial fn highlight text links -> r : text~Bytes, links~(Bytes -> Bytes -> Bool -> Option Bytes), r~Bytes
    match syntax.lex text
        Ok ls -> bytes.concat (list.reverse (lines_html ls 1 START links []))
        Err _ -> escape text

# ── Links ────────────────────────────────────────────────────────────────────

# Something a link can name: its full name (`std.list`, `std.list.sort`,
# `std.json.Json.Null`), where its documentation is (from the
# documentation's directory), and whether it is exported.
export record Symbol
    name~String
    url~String
    exported~Bool

# A warning about a page, at byte `at` of it.
export record Warning
    code~String
    message~String
    at~Nat
    help~String

fn is_name_start c : c~U8
    (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or c == '_'

fn is_name_char c : c~U8
    is_name_start c or (c >= '0' and c <= '9')

# Whether `b` is a dotted path of names (`list.sort`).
partial fn is_path b : b~Bytes
    len b > 0 and path_from b 0 True

partial fn path_from b i first : b~Bytes, i~Nat, first~Bool
    if i >= len b
        not first
    else if first
        is_name_start b[i] and path_from b (i + 1) False
    else if b[i] == '.'
        path_from b (i + 1) True
    else
        is_name_char b[i] and path_from b (i + 1) False

# A link's label without the backticks that show it as code.
partial fn unquoted label -> r : label~String, r~Bytes
    let b = trim (string.bytes label)
    if len b > 2 and b[0] == '`' and b[len b - 1] == '`' then part b 1 (len b - 1) else b

partial fn symbol_named syms name -> r : syms~List Symbol, name~String, r~Option Symbol
    match syms
        s :: rest -> if s.name == name then Some s else symbol_named rest name
        []        -> None

# The symbol `label` names: by its full name, or through a name in `scope`
# (`(name, full name)`: a module's or a declaration's).
export partial fn lookup syms scope label -> r : syms~List Symbol, scope~List (String, String), label~String,
                                                 r~Option Symbol
    let b = unquoted label
    if not (is_path b)
        None
    else
        match symbol_named syms (as_string b)
            Some s -> Some s
            None   -> through_scope syms scope b

partial fn through_scope syms scope b -> r : syms~List Symbol, scope~List (String, String), b~Bytes,
                                             r~Option Symbol
    let dot = match find b b"." 0
        Some k -> k
        None   -> len b
    let first = as_string (part b 0 dot)
    let rest = as_string (from b dot)
    match scope
        (n, full) :: more ->
            if n == first
                match symbol_named syms (full ++ rest)
                    Some s -> Some s
                    None   -> through_scope syms more b
            else
                through_scope syms more b
        []                -> None

# The names `import` lines in `text` bring into scope.
export partial fn imports_of text -> r : text~Bytes, r~List (String, String)
    flatten (list.map import_names (lines_of text))

partial fn flatten xss -> r : xss~List (List a), r~List a
    match xss
        []         -> []
        xs :: rest -> xs ++ flatten rest

# `import a.b`, `import a.b as c`, `import a.b (X, Y)`.
partial fn import_names line -> r : line~Bytes, r~List (String, String)
    let l = trim (if starts line b"#!" then from line 2 else line)
    if not (starts l b"import ")
        []
    else
        let rest = trim (from l 7)
        let e = name_end rest 0
        let full = as_string (part rest 0 e)
        let after = trim (from rest e)
        let named = trim (from after 3)
        let alias = if starts after b"as " then as_string (part named 0 (name_end named 0)) else last_segment full
        let names = if starts after b"("
            list.map (\n -> (n, full ++ "." ++ n)) (names_in (part after 1 (len after)) 0 0 [])
        else
            []
        (alias, full) :: names

partial fn name_end b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b and (is_name_char b[i] or b[i] == '.') then name_end b (i + 1) else i

partial fn last_segment full -> r : full~String, r~String
    let b = string.bytes full
    as_string (from b (after_dot b (len b)))

partial fn after_dot b j -> r : b~Bytes, j~Nat, r~Nat
    if j > 0 and j <= len b and b[j - 1] != '.' then after_dot b (j - 1) else j

partial fn names_in b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List String, r~List String
    if i >= len b or b[i] == ')'
        list.reverse (add_name b start i acc)
    else if b[i] == ','
        names_in b (i + 1) (i + 1) (add_name b start i acc)
    else
        names_in b start (i + 1) acc

partial fn add_name b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List String, r~List String
    let n = trim (part b start i)
    if len n > 0 then as_string n :: acc else acc

# The unresolved references that are paths: W030 (no such symbol), or W031
# (one that isn't exported).
partial fn link_warnings syms scope refs -> r : syms~List Symbol, scope~List (String, String),
                                                refs~List Reference, r~List Warning
    match refs
        x :: rest ->
            let b = unquoted x.label
            let here = if not (is_path b)
                []
            else
                match lookup syms scope x.label
                    Some s ->
                        if s.exported
                            []
                        else
                            [Warning "W031" ("`" ++ as_string b ++ "` isn't exported, so it has no documentation") x.span.start
                             ""]
                    None   ->
                        let near = closest syms (as_string b)
                        let help = if near == "" then "" else "the closest name is `" ++ near ++ "`"
                        [Warning "W030" ("no symbol `" ++ as_string b ++ "` to link to") x.span.start help]
            here ++ link_warnings syms scope rest
        []        -> []

# The exported symbol whose last part is closest to `name`'s (with at most a
# third of its characters changed), if any.
partial fn closest syms name -> r : syms~List Symbol, name~String, r~String
    let target = string.bytes (last_segment name)
    closest_from syms target "" (len target / 3 + 1)

partial fn closest_from syms target best d -> r : syms~List Symbol, target~Bytes, best~String, d~Nat, r~String
    match syms
        s :: rest ->
            let e = distance (string.bytes (last_segment s.name)) target
            if s.exported and e < d then closest_from rest target s.name e else closest_from rest target best d
        []        -> best

# Levenshtein distance, row by row.
partial fn distance a b -> r : a~Bytes, b~Bytes, r~Nat
    let first = list.map (\j -> j) (upto 0 (len b))
    match list.head (list.reverse (rows a b 0 first))
        Some n -> n
        None   -> 0

partial fn upto i n -> r : i~Nat, n~Nat, r~List Nat
    if i > n then [] else i :: upto (i + 1) n

partial fn rows a b i prev -> r : a~Bytes, b~Bytes, i~Nat, prev~List Nat, r~List Nat
    if i >= len a then prev else rows a b (i + 1) (next_row a[i] b 0 prev [i + 1])

partial fn next_row c b j prev acc -> r : c~U8, b~Bytes, j~Nat, prev~List Nat, acc~List Nat, r~List Nat
    match prev
        diag :: up :: more ->
            let left = match acc
                x :: _ -> x
                []     -> 0
            let cost = if j < len b and b[j] == c then 0 else 1
            let v = min3 (up + 1) (left + 1) (diag + cost)
            next_row c b (j + 1) (up :: more) (v :: acc)
        _                  -> list.reverse acc

fn min3 a b c -> r : a~Nat, b~Nat, c~Nat, r~Nat
    let m = if a < b then a else b
    if m < c then m else c

# ── Code blocks ──────────────────────────────────────────────────────────────

# A code block's info string's parts: its language, then attributes
# (`checkers,compile_fail,E0450`).
partial fn info_parts info -> r : info~String, r~List Bytes
    list.map trim (split_commas (string.bytes (markdown.language info)) 0 0 [])

partial fn split_commas b start i acc -> r : b~Bytes, start~Nat, i~Nat, acc~List Bytes, r~List Bytes
    if i >= len b
        list.reverse (part b start i :: acc)
    else if b[i] == ','
        split_commas b (i + 1) (i + 1) (part b start i :: acc)
    else
        split_commas b start (i + 1) acc

# Whether a block with this info string is Checkers: no language, or
# `checkers`.
export partial fn is_checkers info : info~String
    match info_parts info
        lang :: _ -> lang == b"" or lang == b"checkers"
        []        -> True

partial fn has_attr info a : info~String, a~Bytes
    list.contains (list.drop 1 (info_parts info)) a

# The error code `compile_fail` names, if any (`E0450`).
partial fn expected_error info -> r : info~String, r~Bytes
    match list.head (list.reverse (list.drop 1 (info_parts info)))
        Some a -> if len a == 5 and a[0] == 'E' then a else b""
        None   -> b""

# A code block, as compiled: each line's text and where it starts on the
# page (a hidden `module` line, where the block starts).
record Sample
    info~String
    source~String
    name~String
    lines~List (Bytes, Nat)
    shown~Bytes

# A block's lines and their spans: `#!` lines compiled but not shown, a
# hidden `module` line if it has none, and a hidden import of the module
# the page documents unless the block imports it (D164).
partial fn sample documented k info source spans start -> r : documented~Option (String, List String), k~Nat, info~String,
                                                              source~String, spans~List Span, start~Nat, r~Sample
    let ls = zip (lines_of (string.bytes source)) spans
    let compiled = list.map compiled_line ls
    let shown = bytes.concat (list.map (\l -> bytes.concat [l, b"\n"]) (shown_lines ls))
    match module_named compiled
        Some name -> Sample info source name (with_own documented name start compiled) shown
        None      ->
            let name = string.format"sample_{k}"
            let header = (string.bytes ("module " ++ name), start)
            Sample info source name (header :: with_own documented name start compiled) shown

# A block's lines with the documented module's import after its `module`
# line (or first, when that line is to be added): unless the block is that
# module or imports it itself.
partial fn with_own documented name start ls -> r : documented~Option (String, List String), name~String,
                                                    start~Nat, ls~List (Bytes, Nat), r~List (Bytes, Nat)
    match documented
        None            -> ls
        Some (m, names) ->
            if m == name or list.contains (list.map (\x -> imports_module x m) ls) True
                ls
            else
                let line = (string.bytes (import_line m names), start)
                if list.contains (list.map is_module_line ls) True then after_module line ls else line :: ls

fn import_line m names -> r : m~String, names~List String, r~String
    match names
        []        -> "import " ++ m
        n :: rest -> "import " ++ m ++ " (" ++ string.concat (n :: list.map (\x -> ", " ++ x) rest) ++ ")"

partial fn imports_module x m : x~(Bytes, Nat), m~String
    match x
        (l, _) ->
            let t = trim l
            let name = string.bytes m
            let after = 7 + len name
            starts t b"import " and bytes.matches_at t 7 name
                and (len t == after or bytes.matches_at t after b" " or bytes.matches_at t after b"(")

partial fn is_module_line x : x~(Bytes, Nat)
    match x
        (l, _) -> starts (trim l) b"module "

partial fn after_module line ls -> r : line~(Bytes, Nat), ls~List (Bytes, Nat), r~List (Bytes, Nat)
    match ls
        x :: rest -> if is_module_line x then x :: line :: rest else x :: after_module line rest
        []        -> [line]

partial fn zip ls spans -> r : ls~List Bytes, spans~List Span, r~List (Bytes, Nat)
    match (ls, spans)
        (l :: lr, s :: sr) -> (l, s.start) :: zip lr sr
        (l :: lr, [])      -> (l, 0) :: zip lr []
        _                  -> []

fn is_hidden l : l~Bytes
    bytes.matches_at l 0 b"#!"

partial fn compiled_line x -> r : x~(Bytes, Nat), r~(Bytes, Nat)
    let (l, at) = x
    if is_hidden l
        let n = if bytes.matches_at l 2 b" " then 3 else 2
        (from l n, at + n)
    else
        (l, at)

partial fn shown_lines ls -> r : ls~List (Bytes, Nat), r~List Bytes
    match ls
        (l, _) :: rest -> if is_hidden l then shown_lines rest else l :: shown_lines rest
        []             -> []

partial fn module_named ls -> r : ls~List (Bytes, Nat), r~Option String
    match ls
        (l, _) :: rest ->
            let t = trim l
            if blank t or starts t b"#"
                module_named rest
            else if starts t b"module "
                Some (as_string (trim (from t 7)))
            else
                None
        []             -> None

partial fn has_main s : s~Sample
    list.contains (list.map is_main s.lines) True

partial fn is_main x : x~(Bytes, Nat)
    match x
        (l, _) -> starts (trim l) b"fn main " or starts (trim l) b"export fn main "

# What compiling (and running) a block gave: its warnings, and the output
# shown after it, if any.
record Outcome
    warnings~List Warning
    output~Bytes

# What a page needs to compile its code: the compiler, a directory to write
# blocks in (blocks on one page may import each other), and flags for it
# (packages).
# How a page's blocks are compiled: `ckc`, the directory the blocks are
# compiled as if they were in (a module page's package, so that a block may
# import its modules as the module does; else a directory of the page's
# own), and `ckc`'s flags. The blocks are given to `ckc` as an overlay
# (D120), not written there.
export record Compiler
    ckc~String
    work~String
    flags~List String

partial fn file_of c s -> r : c~Compiler, s~Sample, r~String
    # A module `a.b` is the file `a/b.ck` (D53).
    c.work ++ "/" ++ string.concat_map (\ch -> if ch == c'.' then "/" else string.from_char ch) s.name ++ ".ck"

# The overlay: every block of the page, at its file, so one may import
# another.
partial fn overlay_of c ss -> r : c~Compiler, ss~List Sample, r~Bytes
    let entries = list.map (\s -> (file_of c s, Str (as_string (sample_text s)))) ss
    string.bytes (json.render (rpc.obj entries))

partial fn compile c s all fs p -> r : c~Compiler, s~Sample, all~Bytes, fs~Fs, p~Proc, r~Outcome
    let file = file_of c s
    let fail = has_attr s.info b"compile_fail"
    let start = match s.lines
        (_, at) :: _ -> at
        []           -> 0
    if fail
        match proc.run c.ckc (c.flags ++ ["check", "--overlay", "-", file]) all p
            Err e  -> Outcome [Warning "W032" ("could not run `" ++ c.ckc ++ "`: " ++ files.describe e) start ""] b""
            Ok out ->
                let report = without_dir (bytes.concat [out.stdout, out.stderr]) (string.bytes (c.work ++ "/"))
                let code = expected_error s.info
                if out.code == 0
                    Outcome [Warning "W033" "this block compiles, but is marked `compile_fail`" start ""] b""
                else if len code > 0 and find report (bytes.concat [b"error[", code, b"]"]) 0 == None
                    Outcome [Warning "W033" ("this block fails, but not with " ++ as_string code) start ""] report
                else
                    Outcome [] report
    else
        match proc.run c.ckc (c.flags ++ ["check", "--json", "--overlay", "-", file]) all p
            Err e  -> Outcome [Warning "W032" ("could not run `" ++ c.ckc ++ "`: " ++ files.describe e) start ""] b""
            Ok out ->
                let ws = diagnostics s (lines_of out.stdout)
                if ws != [] or has_attr s.info b"no_run" or not (has_main s)
                    Outcome ws b""
                else
                    run c s file all p

partial fn run c s file all p -> r : c~Compiler, s~Sample, file~String, all~Bytes, p~Proc, r~Outcome
    let start = match s.lines
        (_, at) :: _ -> at
        []           -> 0
    match proc.run c.ckc (c.flags ++ ["run", "--overlay", "-", "--threads", "1", file]) all p
        Err e  -> Outcome [Warning "W034" ("could not run `" ++ c.ckc ++ "`: " ++ files.describe e) start ""] b""
        Ok out ->
            let output = without_dir (bytes.concat [out.stdout, out.stderr]) (string.bytes (c.work ++ "/"))
            if out.code == 0
                Outcome [] output
            else
                Outcome [Warning "W034" string.format"this block's `main` exits with code {out.code}" start ""] output

# `b` without each `dir` in it (the paths of the files a report names).
partial fn without_dir b dir -> r : b~Bytes, dir~Bytes, r~Bytes
    match find b dir 0
        Some k -> bytes.concat [part b 0 k, without_dir (from b (k + len dir)) dir]
        None   -> b

# The diagnostics `ckc check --json` gives for the block, as W032 at their
# places on the page.
partial fn diagnostics s lines -> r : s~Sample, lines~List Bytes, r~List Warning
    match lines
        l :: rest ->
            let here = match json.parse l
                Ok j  ->
                    if rpc.str_at ["kind"] j == Some "diagnostic"
                        let (line, col) = match rpc.at ["start"] j
                            Some (Arr [a, b]) -> (nat_of a, nat_of b)
                            _                 -> (0, 0)
                        let at = match list.head (list.drop line s.lines)
                            Some (_, a) -> a + col
                            None        -> 0
                        let code = match rpc.str_at ["code"] j
                            Some c -> c
                            None   -> ""
                        let message = match rpc.str_at ["message"] j
                            Some m -> m
                            None   -> ""
                        [Warning "W032" ("this code has " ++ code ++ ": " ++ message) at ""]
                    else
                        []
                Err _ -> []
            here ++ diagnostics s rest
        []        -> []

partial fn nat_of j -> r : j~Json, r~Nat
    match rpc.nat_of j
        Some n -> n
        None   -> 0

# ── Pages ────────────────────────────────────────────────────────────────────

# What a page links to and compiles with.
export record Context
    symbols~List Symbol
    scope~List (String, String)     # names in scope, and their full names
    base~String                     # the way from the page to the symbols' documentation
    compiler~Compiler
    links~(Bytes -> Bytes -> Bool -> Option Bytes)   # names in signatures (§15.6)
    documented~Option (String, List String)          # the module documented, and its exports: its blocks import it (D164)

# The code blocks of blocks, in order.
partial fn code_blocks bs -> r : bs~List Block, r~List (String, String, List Span, Nat)
    match bs
        b :: rest -> block_code b ++ code_blocks rest
        []        -> []

partial fn block_code b -> r : b~Block, r~List (String, String, List Span, Nat)
    match b
        Code info text ls s -> [(info, text, ls, s.start)]
        Quote xs _          -> code_blocks xs
        Bullets _ is _      -> item_code is
        Numbered _ _ is _   -> item_code is
        _                   -> []

partial fn item_code is -> r : is~List Item, r~List (String, String, List Span, Nat)
    match is
        i :: rest -> code_blocks i.blocks ++ item_code rest
        []        -> []

partial fn only_checkers xs -> r : xs~List (String, String, List Span, Nat), r~List (String, String, List Span, Nat)
    match xs
        (info, text, ls, at) :: rest ->
            if is_checkers info and not (has_attr info b"ignore")
                (info, text, ls, at) :: only_checkers rest
            else
                only_checkers rest
        []                           -> []

partial fn numbered_samples documented xs k -> r : documented~Option (String, List String),
                                                   xs~List (String, String, List Span, Nat), k~Nat, r~List Sample
    match xs
        (info, text, ls, at) :: rest -> sample documented k info text ls at :: numbered_samples documented rest (k + 1)
        []                           -> []

partial fn sample_text s -> r : s~Sample, r~Bytes
    bytes.concat (list.map (\x -> line_of x) s.lines)

fn line_of x -> r : x~(Bytes, Nat), r~Bytes
    match x
        (l, _) -> bytes.concat [l, b"\n"]

partial fn compile_all c ss all fs p -> r : c~Compiler, ss~List Sample, all~Bytes, fs~Fs, p~Proc, r~List (Sample, Outcome)
    match ss
        s :: rest -> (s, compile c s all fs p) :: compile_all c rest all fs p
        []        -> []

# A compiled block as HTML: its shown lines highlighted, then its output.
partial fn block_html s res links -> r : s~Sample, res~Outcome, links~(Bytes -> Bytes -> Bool -> Option Bytes), r~Bytes
    if len s.shown == 0 and len res.output == 0 then b"" else shown_html s res links

partial fn shown_html s res links -> r : s~Sample, res~Outcome, links~(Bytes -> Bytes -> Bool -> Option Bytes), r~Bytes
    let fails = has_attr s.info b"compile_fail"
    let cls = if fails then b" class=\"fails\" title=\"This code doesn't compile.\"" else b""
    let code = bytes.concat [b"<pre", cls, b"><code class=\"language-checkers\">", highlight s.shown links,
                             b"</code></pre>"]
    if len res.output == 0
        code
    else
        bytes.concat [code, b"\n<pre class=\"output\"><code>", escape res.output, b"</code></pre>"]

# A Checkers block's HTML: as compiled, or (`ignore`) only highlighted.
partial fn lookup_output outputs links info body -> r : outputs~List (String, Bytes),
                                                        links~(Bytes -> Bytes -> Bool -> Option Bytes), info~String,
                                                        body~String, r~Option String
    if not (is_checkers info)
        None
    else
        match outputs
            (text, html) :: rest -> if text == body then Some (as_string html) else lookup_output rest links info body
            []                   ->
                let shown = bytes.concat (list.map (\l -> bytes.concat [l, b"\n"]) (shown_lines (zip (lines_of (string.bytes body)) [])))
                Some (as_string (bytes.concat [b"<pre><code class=\"language-checkers\">", highlight shown links,
                                               b"</code></pre>"]))

# A heading with its anchor (`id`), and a paragraph that is a table, as HTML.
partial fn page_block text b -> r : text~Bytes, b~Block, r~Block
    match b
        Heading level xs s ->
            let n = string.bytes (string.display level [])
            let id = slug (string.bytes (markdown.plain xs))
            Html (as_string (bytes.concat [b"<h", n, b" id=\"", id, b"\">", inline_html xs, b"</h", n, b">"])) s
        Paragraph xs s     ->
            let rows = lines_of (part text s.start s.stop)
            match rows
                head :: rule :: body ->
                    if list.all table_row rows and separator rule then Html (as_string (table head body)) s else b
                _                    -> b
        Quote bs s         -> Quote (list.map (page_block text) bs) s
        Bullets t is s     -> Bullets t (list.map (page_item text) is) s
        Numbered n t is s  -> Numbered n t (list.map (page_item text) is) s
        _                  -> b

partial fn page_item text i -> r : text~Bytes, i~Item, r~Item
    Item (list.map (page_block text) i.blocks) i.span

# Inlines as HTML, without a paragraph around them.
partial fn inline_html xs -> r : xs~List Inline, r~Bytes
    let h = string.bytes (markdown.to_html (Document [Paragraph xs (Span 0 0)] [] []))
    if len h >= 8 then part h 3 (len h - 5) else b""

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

partial fn table head rows -> r : head~Bytes, rows~List Bytes, r~Bytes
    let th = row_html b"th" head
    let trs = list.map (\r -> row_html b"td" r) rows
    bytes.concat ([b"<table>\n<thead>\n", th, b"</thead>\n<tbody>\n"] ++ trs ++ [b"</tbody>\n</table>"])

partial fn row_html tag row -> r : tag~Bytes, row~Bytes, r~Bytes
    let cells = cells_of (trim row)
    let tds = list.map (\c -> bytes.concat [b"<", tag, b">", cell_html (unescape_pipes (trim c) 0 0 []), b"</", tag,
                                            b">"]) cells
    bytes.concat ([b"<tr>"] ++ tds ++ [b"</tr>\n"])

partial fn cell_html b -> r : b~Bytes, r~Bytes
    match (markdown.parse (as_string b)).blocks
        [Paragraph xs _] -> inline_html (list.map links_inline xs)
        _                -> escape b

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

# Links to `.md` pages lead to their `.html` twins.
partial fn links_block b -> r : b~Block, r~Block
    match b
        Paragraph xs s    -> Paragraph (list.map links_inline xs) s
        Heading l xs s    -> Heading l (list.map links_inline xs) s
        Quote bs s        -> Quote (list.map links_block bs) s
        Bullets t is s    -> Bullets t (list.map links_item is) s
        Numbered n t is s -> Numbered n t (list.map links_item is) s
        _                 -> b

partial fn links_item i -> r : i~Item, r~Item
    Item (list.map links_block i.blocks) i.span

partial fn links_inline x -> r : x~Inline, r~Inline
    match x
        Link t xs ref s -> Link (Target (as_string (html_target (string.bytes t.url))) t.title) (list.map links_inline xs) ref s
        Emph xs s       -> Emph (list.map links_inline xs) s
        Strong xs s     -> Strong (list.map links_inline xs) s
        _               -> x

partial fn html_target url -> r : url~Bytes, r~Bytes
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

# A page as HTML, and its warnings. Its links resolve in `cx`'s scope and
# through its code blocks' imports (hidden lines too); its Checkers blocks
# are compiled, and run if they have `main`.
export partial fn render text cx fs p -> r : text~Bytes, cx~Context, fs~Fs, p~Proc, r~(Bytes, List Warning)
    let source = as_string text
    let plain = markdown.parse source
    let samples = numbered_samples cx.documented (only_checkers (code_blocks plain.blocks)) 1
    let scope = cx.scope ++ flatten (list.map (\s -> imports_of (sample_text s)) samples)
    let syms = cx.symbols
    let base = cx.base
    let resolve = \label -> found_target syms scope base label
    let d = markdown.parse_with resolve source
    let results = compile_all cx.compiler samples (overlay_of cx.compiler samples) fs p
    let outputs = list.map (\x -> output_of x cx.links) results
    let links = cx.links
    let code = \info body -> lookup_output outputs links info body
    let shown = Document (list.map (page_block text) (list.map links_block d.blocks)) d.definitions d.unresolved
    let html = string.bytes (markdown.to_html_with code shown)
    let warnings = link_warnings syms scope d.unresolved ++ flatten (list.map result_warnings results)
    (html, warnings)

partial fn found_target syms scope base label -> r : syms~List Symbol, scope~List (String, String), base~String,
                                                     label~String, r~Option Target
    match lookup syms scope label
        Some s -> if s.exported then Some (Target (base ++ s.url) None) else None
        None   -> None

partial fn output_of x links -> r : x~(Sample, Outcome), links~(Bytes -> Bytes -> Bool -> Option Bytes),
                                    r~(String, Bytes)
    match x
        (s, res) -> (s.source, block_html s res links)

fn result_warnings x -> r : x~(Sample, Outcome), r~List Warning
    match x
        (_, res) -> res.warnings

# ── The page as Markdown ─────────────────────────────────────────────────────

# The page's Markdown as it is shown: its Checkers blocks' `#!` lines left
# out, as the HTML leaves them out (D148 g), and a block of such lines
# alone with its fences.
export partial fn without_hidden text -> r : text~Bytes, r~Bytes
    let doc = markdown.parse (as_string text)
    let cuts = list.sort_as first_of (hidden_ranges text (code_nodes doc.blocks))
    cut_out text cuts 0

fn first_of x -> n : x~(Nat, Nat), n~Nat
    match x
        (a, _) -> a

# The Checkers code blocks: each line's span, and the block's.
partial fn code_nodes bs -> r : bs~List Block, r~List (List Span, Span)
    match bs
        b :: rest ->
            let here = match b
                Code info _ ls s  -> if is_checkers info then [(ls, s)] else []
                Quote xs _        -> code_nodes xs
                Bullets _ is _    -> item_nodes is
                Numbered _ _ is _ -> item_nodes is
                _                 -> []
            here ++ code_nodes rest
        []        -> []

partial fn item_nodes is -> r : is~List Item, r~List (List Span, Span)
    match is
        i :: rest -> code_nodes i.blocks ++ item_nodes rest
        []        -> []

# The byte ranges to leave out: each hidden line's whole line, or a block's
# whole lines when all of its lines are hidden.
partial fn hidden_ranges text bs -> r : text~Bytes, bs~List (List Span, Span), r~List (Nat, Nat)
    match bs
        (ls, s) :: rest ->
            let hidden = hidden_lines text ls
            let mine = if ls != [] and list.length hidden == list.length ls
                [(line_start text s.start, line_end text (if s.stop > 0 then s.stop - 1 else 0))]
            else
                list.map (\x -> (line_start text x.start, line_end text x.start)) hidden
            mine ++ hidden_ranges text rest
        []              -> []

partial fn hidden_lines text ls -> r : text~Bytes, ls~List Span, r~List Span
    match ls
        l :: rest -> if bytes.matches_at text l.start b"#!" then l :: hidden_lines text rest else hidden_lines text rest
        []        -> []

# The first byte of the line `i` is on.
partial fn line_start text i -> r : text~Bytes, i~Nat, r~Nat
    if i == 0 or i > len text then (if i > len text then len text else 0) else if text[i - 1] == '\n' then i else line_start text (i - 1)

# Just after the end of the line `i` is on (its newline included).
partial fn line_end text i -> r : text~Bytes, i~Nat, r~Nat
    if i >= len text then len text else if text[i] == '\n' then i + 1 else line_end text (i + 1)

# `text` from `at` without the ranges `cuts` (sorted).
partial fn cut_out text cuts at -> r : text~Bytes, cuts~List (Nat, Nat), at~Nat, r~Bytes
    match cuts
        (a, b) :: rest ->
            let keep = if a > at and a <= len text then bytes.slice text at a else b""
            bytes.concat [keep, cut_out text rest (if b > at then b else at)]
        []             -> if at < len text then bytes.slice text at (len text) else b""
