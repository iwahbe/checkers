# ck/syntax.ck — Checkers source as tokens and lines, keeping comments and
# blank lines (D93). The lexer follows SPEC §9.1; the layout pass assigns
# each line its block level, or marks it as continuing the line before.

module ck.syntax

import std.bytes
import std.list (reverse)
import std.list

# ── Tokens ───────────────────────────────────────────────────────────────────

export enum Kind
    Name                       # lower-case names, keywords, `and`, `or`, `implies`
    Upper                      # capitalised names
    Number
    Literal                    # string, bytes, byte and char literals
    Punct                      # operators and punctuation
    Comment

# A token: its text, the column it starts at and its width (in characters),
# and whether it follows whitespace or the start of its line.
export record Tok
    kind~Kind
    text~Bytes
    col~Nat
    wide~Nat
    spaced~Bool

# A physical line: its number (from 1), its code and its trailing comment.
export record Line
    num~Nat
    toks~List Tok
    comment~Option Tok

export record SyntaxError
    line~Nat
    col~Nat
    message~String

# A scanned token: its kind and where it stops (`i < stop <= e`).
record Scan i e : i~ghost Nat, e~ghost Nat
    kind~Kind
    stop~Nat, i < stop, stop <= e

fn peek src i e -> r : src~Bytes, i~Nat, e~Nat, e <= len src, r~Option U8
    if i < e then Some src[i] else None

fn is_lower c : c~U8
    ('a' <= c and c <= 'z') or c == '_'

fn is_upper c : c~U8
    'A' <= c and c <= 'Z'

fn is_digit c : c~U8
    '0' <= c and c <= '9'

fn is_word c : c~U8
    is_lower c or is_upper c or is_digit c

# A byte that continues a UTF-8 sequence (it doesn't start a character).
fn is_cont c : c~U8
    c >= 0x80 and c < 0xC0

# The number of characters in `src[i..j]`.
fn width src i j -> w : src~Bytes, i~Nat, j~Nat, i <= j, j <= len src, w~Nat
    decreasing j - i
    if i == j then 0 else (if is_cont src[i] then 0 else 1) + width src (i + 1) j

fn word_end src i e -> j : src~Bytes, i~Nat, e~Nat, i <= e, e <= len src, j~Nat, i <= j, j <= e
    decreasing e - i
    if i < e and is_word src[i] then word_end src (i + 1) e else i

# Just past the quote `q` that closes a literal whose body starts at `i`.
fn quote_end src i e q -> r : src~Bytes, i~Nat, e~Nat, i <= e, e <= len src, q~U8,
                              r~Option (j~Nat, i < j, j <= e)
    decreasing e - i
    match peek src i e
        None   -> None
        Some c ->
            if c == q
                Some (i + 1)
            else if c == '\\'
                if i + 2 <= e
                    match quote_end src (i + 2) e q
                        None   -> None
                        Some j -> Some j
                else
                    None
            else
                match quote_end src (i + 1) e q
                    None   -> None
                    Some j -> Some j

# Just past the quote that closes a template whose body starts at `i`: its
# holes, `{…}`, may hold strings and templates; `{{` and `}}` are braces.
fn template_end src i e -> r : src~Bytes, i~Nat, e~Nat, i <= e, e <= len src,
                               r~Option (j~Nat, i < j, j <= e)
    decreasing e - i
    match peek src i e
        None   -> None
        Some c ->
            if c == '"'
                Some (i + 1)
            else if c == '\\' or two src i e '{' '{' or two src i e '}' '}'
                if i + 2 <= e
                    match template_end src (i + 2) e
                        None   -> None
                        Some j -> Some j
                else
                    None
            else if c == '{'
                match hole_end src (i + 1) e 0
                    None   -> None
                    Some k ->
                        match template_end src k e
                            None   -> None
                            Some j -> Some j
            else
                match template_end src (i + 1) e
                    None   -> None
                    Some j -> Some j

# Just past the `}` that closes a template's hole whose inside starts at
# `i`, `depth` brackets being open in it.
fn hole_end src i e depth -> r : src~Bytes, i~Nat, e~Nat, i <= e, e <= len src, depth~Nat,
                                 r~Option (j~Nat, i < j, j <= e)
    decreasing e - i
    match peek src i e
        None   -> None
        Some c ->
            if c == '}' and depth == 0
                Some (i + 1)
            else if c == '"' or c == '\''
                let inner = if c == '"' and i > 0 and is_word src[i - 1]
                    template_end src (i + 1) e
                else
                    quote_end src (i + 1) e c
                match inner
                    None   -> None
                    Some k ->
                        match hole_end src k e depth
                            None   -> None
                            Some j -> Some j
            else
                let d = if c == '(' or c == '[' or c == '{'
                    depth + 1
                else if (c == ')' or c == ']' or c == '}') and depth > 0
                    depth - 1
                else
                    depth
                match hole_end src (i + 1) e d
                    None   -> None
                    Some j -> Some j

fn error n col msg -> r : n~Nat, col~Nat, msg~String, r~SyntaxError
    SyntaxError n col msg

# A literal whose body starts at `body`, closed by `q`.
fn literal src i body e q n col -> r : src~Bytes, i~Nat, body~Nat, i < body, body <= e, e <= len src,
                                       q~U8, n~Nat, col~Nat,
                                       r~Result (Scan i e) SyntaxError
    match quote_end src body e q
        Some j -> Ok (Scan Literal j)
        None   -> Err (error n col "unterminated literal")

fn two src i e a b : src~Bytes, i~Nat, e~Nat, e <= len src, a~U8, b~U8
    i + 1 < e and src[i] == a and src[i + 1] == b

fn two_char src i e : src~Bytes, i~Nat, e~Nat, e <= len src
    two src i e '+' '+' or two src i e ':' ':' or two src i e '=' '=' or two src i e '!' '='
        or two src i e '<' '=' or two src i e '>' '=' or two src i e '-' '>'

fn one_char c : c~U8
    c == '+' or c == '-' or c == '*' or c == '/' or c == '%' or c == '<' or c == '>'
        or c == '$' or c == '.' or c == '(' or c == ')' or c == '[' or c == ']'
        or c == '{' or c == '}' or c == ',' or c == ':' or c == '~' or c == '\\'
        or c == '|' or c == '='

# A template, glued to its tag, whose body starts at `body`.
fn template src i body e n col -> r : src~Bytes, i~Nat, body~Nat, i < body, body <= e, e <= len src,
                                      n~Nat, col~Nat,
                                      r~Result (Scan i e) SyntaxError
    match template_end src body e
        Some j -> Ok (Scan Literal j)
        None   -> Err (error n col "unterminated literal")

# One token starting at `i` (not a space or a comment); `tagged`: a name is
# glued before it, so a string there is a template.
fn scan src i e n col tagged -> r : src~Bytes, i~Nat, e~Nat, i < e, e <= len src, n~Nat, col~Nat, tagged~Bool,
                                    r~Result (Scan i e) SyntaxError
    let c = src[i]
    if c == 'c' and i + 1 < e and src[i + 1] == '\''
        literal src i (i + 2) e '\'' n col
    else if c == 'b' and i + 1 < e and src[i + 1] == '"'
        literal src i (i + 2) e '"' n col
    else if is_lower c
        Ok (Scan Name (word_end src (i + 1) e))
    else if is_upper c
        Ok (Scan Upper (word_end src (i + 1) e))
    else if is_digit c
        Ok (Scan Number (word_end src (i + 1) e))
    else if c == '\''
        literal src i (i + 1) e '\'' n col
    else if c == '"' and tagged
        template src i (i + 1) e n col
    else if c == '"'
        literal src i (i + 1) e '"' n col
    else if two_char src i e
        Ok (Scan Punct (i + 2))
    else if one_char c
        Ok (Scan Punct (i + 1))
    else
        Err (error n col "unexpected character")

fn is_space c : c~U8
    c == ' ' or c == '\r' or c == '\t'

# The comment's text, without trailing spaces.
fn trim_end src i j -> k : src~Bytes, i~Nat, j~Nat, i <= j, j <= len src, k~Nat, i <= k, k <= j
    decreasing j - i
    if i < j and is_space src[j - 1] then trim_end src i (j - 1) else j

# Lex the line `src[ls..e]` from `i`; `col` is the column of `i`.
fn lex_line src ls i e n col acc -> r : src~Bytes, ls~Nat, i~Nat, e~Nat, ls <= i, i <= e, e <= len src,
                                        n~Nat, col~Nat, acc~List Tok,
                                        r~Result Line SyntaxError
    decreasing e - i
    match peek src i e
        None   -> Ok (Line n (reverse acc) None)
        Some c ->
            if c == '\t' and acc == []
                Err (error n col "tabs are not allowed in indentation; use spaces")
            else if is_space c
                lex_line src ls (i + 1) e n (col + 1) acc
            else
                let spaced = i == ls or is_space src[i - 1]
                if c == '#'
                    let j = trim_end src i e
                    Ok (Line n (reverse acc) (Some (Tok Comment (bytes.slice src i j) col (width src i j) spaced)))
                else
                    let tagged = match acc
                        t :: _ -> not spaced and tag_name t
                        []     -> False
                    let s = try scan src i e n col tagged
                    let w = width src i s.stop
                    let t = Tok s.kind (bytes.slice src i s.stop) col w spaced
                    lex_line src ls s.stop e n (col + w) (t :: acc)

# A name a template may be glued to: not a keyword or `and`, `or`, `implies`.
fn tag_name t : t~Tok
    match t.kind
        Name -> not (is_keyword t) and t.text != b"and" and t.text != b"or" and t.text != b"implies"
        _    -> False

fn line_end src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and src[i] != '\n' then line_end src (i + 1) else i

fn lex_lines src i n acc -> r : src~Bytes, i~Nat, i <= len src, n~Nat, acc~List Line,
                                r~Result (List Line) SyntaxError
    decreasing len src - i
    if i == len src
        Ok (reverse acc)
    else
        let e = line_end src i
        let l = try lex_line src i i e n 0 []
        if e < len src
            lex_lines src (e + 1) (n + 1) (l :: acc)
        else
            Ok (reverse (l :: acc))

# The physical lines of a file.
export fn lex src -> r : src~Bytes, r~Result (List Line) SyntaxError
    lex_lines src 0 1 []

# ── Token classes ────────────────────────────────────────────────────────────

export fn is_text t s : t~Tok, s~Bytes
    t.text == s

export fn is_punct t s : t~Tok, s~Bytes
    match t.kind
        Punct -> t.text == s
        _     -> False

export fn is_keyword t : t~Tok
    match t.kind
        Name -> list.contains KEYWORDS t.text
        _    -> False

export let KEYWORDS = [b"module", b"import", b"as", b"export", b"abstract", b"transparent", b"fn", b"enum",
                       b"record", b"type", b"let", b"lemma", b"ensures", b"proof", b"have", b"auto", b"admit",
                       b"check", b"match", b"if", b"then", b"else", b"try", b"decreasing", b"partial",
                       b"ghost", b"own", b"comptime", b"when", b"using", b"par", b"class", b"instance", b"forall"]

# A binary operator (§9.4), including `|` between patterns.
export fn is_binop t : t~Tok
    match t.kind
        Punct -> list.contains BINOPS t.text
        Name  -> t.text == b"and" or t.text == b"or" or t.text == b"implies"
        _     -> False

let BINOPS = [b".", b"*", b"/", b"%", b"+", b"-", b"++", b"::", b"==", b"!=", b"<", b"<=", b">",
              b">=", b"$", b"|"]

export fn is_open t : t~Tok
    is_punct t b"(" or is_punct t b"[" or is_punct t b"{"

export fn is_close t : t~Tok
    is_punct t b")" or is_punct t b"]" or is_punct t b"}"

# The bracket depth after `toks`, starting from `d`.
export fn depth_after toks d -> r : toks~List Tok, d~Nat, r~Nat
    match toks
        []        -> d
        t :: rest ->
            if is_open t
                depth_after rest (d + 1)
            else if is_close t and d > 0
                depth_after rest (d - 1)
            else
                depth_after rest d

# ── Layout (§9.1) ────────────────────────────────────────────────────────────

# What a line is: blank, the start of a logical line at a block level, a
# continuation of the logical line before, or a comment on its own, at the
# level of the line it belongs with. A logical line starting a block that a
# continuation line opened (indented past it) is `Nested`; one starting the
# next block of that continuation's logical line, after it, is `Fresh` (§9.1).
export enum Role
    Blank
    Start lvl  : lvl~Nat
    Nested lvl : lvl~Nat
    Fresh lvl  : lvl~Nat
    Cont
    Note lvl   : lvl~Nat

# The block level of a line that starts a logical line.
export fn starts r -> o : r~Role, o~Option Nat
    match r
        Start lvl  -> Some lvl
        Nested lvl -> Some lvl
        Fresh lvl  -> Some lvl
        _          -> None

export record Placed
    role~Role
    line~Line

# Layout state: the open blocks (innermost first: each one's column, and
# whether a continuation line opened it), the bracket depth, the last code
# token so far, the column of the logical line, of the logical line the
# outermost open bracket is on, and of the last physical line, and whether
# that line continued a logical line.
record State
    stack~List (Nat, Bool)
    depth~Nat
    last~Option Tok
    col~Nat
    open~Nat
    line~Nat
    cont~Bool

fn last_of toks -> r : toks~List Tok, r~Option Tok
    match toks
        []        -> None
        [t]       -> Some t
        _ :: rest -> last_of rest

# The last line ends with a binary operator (not `.`) or a comma.
fn open_ended st : st~State
    match st.last
        Some t -> (is_binop t and not (is_punct t b".")) or is_punct t b","
        None   -> False

# A keyword that only starts a line, never inside brackets (D142 e).
fn starts_only t : t~Tok
    is_keyword t and list.contains LINE_KEYWORDS t.text

let LINE_KEYWORDS = [b"module", b"import", b"export", b"fn", b"partial", b"enum", b"record", b"type",
                     b"lemma", b"class", b"instance", b"check", b"let", b"have", b"when", b"ensures",
                     b"proof", b"decreasing"]

# Brackets left open are closed by such a line at or left of their own.
fn closes st first : st~State, first~Tok
    st.depth > 0 and first.col <= st.open and starts_only first

# A line starting with an operator or `:` continues the one before; one
# starting with a sign (`-1`, glued to what follows, D169) doesn't.
fn continues st toks : st~State, toks~List Tok
    match toks
        []            -> False
        first :: rest ->
            let leads = (is_binop first or is_punct first b":") and not (is_sign first rest)
            not (starts_only first) and (st.depth > 0 or leads or open_ended st)

# A `-` glued to the token after it, at the start of a line or after white
# space or an opening bracket: a sign, not a subtraction (D169).
export fn is_sign t rest : t~Tok, rest~List Tok
    match rest
        n :: _ -> is_punct t b"-" and n.col == t.col + t.wide and not (is_close n or is_punct n b",")
        []     -> False

# The level of the innermost open block whose column is at most `col`.
fn level_at stack col -> l : stack~List (Nat, Bool), col~Nat, l~Nat
    match stack
        []             -> 0
        (c, _) :: rest -> if c <= col then list.length rest else level_at rest col

# Close blocks down to `col`: the remaining stack, if `col` is one of its
# columns, or, leaving a block a continuation line opened for a column
# inside its logical line's block, that stack with a new block at `col`
# (true: a fresh block).
fn dedent stack col -> r : stack~List (Nat, Bool), col~Nat, r~Option (List (Nat, Bool), Bool)
    match stack
        []                  -> None
        (c, nested) :: rest ->
            if c == col
                Some (stack, False)
            else if c < col
                None
            else
                match rest
                    (d, _) :: _ if nested and d < col -> Some ((col, False) :: rest, True)
                    _ -> dedent rest col

# The level of the innermost block.
fn level_of stack -> l : stack~List (Nat, Bool), l~Nat
    match stack
        []        -> 0
        _ :: rest -> list.length rest

fn place lines st acc -> r : lines~List Line, st~State, acc~List Placed, r~Result (List Placed) SyntaxError
    match lines
        []        -> Ok (reverse acc)
        l :: rest ->
            match l.toks
                []         ->
                    match l.comment
                        None   -> place rest st (Placed Blank l :: acc)
                        Some c ->
                            # A continuation's comment is indented past the line it continues.
                            let cont = (st.depth > 0 and c.col > st.open) or (open_ended st and c.col > st.col)
                            let role = if cont then Cont else Note (level_at st.stack c.col)
                            place rest st (Placed role l :: acc)
                first :: _ ->
                    let st = if closes st first then State st.stack 0 st.last st.col st.open st.line st.cont else st
                    let cont = st.last != None and continues st l.toks
                    let col = if cont then st.col else first.col
                    let depth = depth_after l.toks st.depth
                    let open = if st.depth == 0 and depth > 0 then col else st.open
                    if cont
                        place rest (State st.stack depth (last_of l.toks) col open first.col True) (Placed Cont l :: acc)
                    else
                        let top = match st.stack
                            []          -> 0
                            (c, _) :: _ -> c
                        if first.col > top
                            if st.last == None
                                Err (error l.num first.col "unexpected indentation at the start of the file")
                            else
                                # Indented past the continuation line before it: that line's block.
                                let nested = st.cont and first.col > st.line
                                let stack = (first.col, nested) :: st.stack
                                let lvl = list.length st.stack
                                let p = Placed (if nested then Nested lvl else Start lvl) l
                                place rest (State stack depth (last_of l.toks) col open first.col False) (p :: acc)
                        else
                            match dedent st.stack first.col
                                None                -> Err (error l.num first.col "unindent does not match any outer indentation level")
                                Some (stack, fresh) ->
                                    let lvl = level_of stack
                                    let p = Placed (if fresh then Fresh lvl else Start lvl) l
                                    place rest (State stack depth (last_of l.toks) col open first.col False) (p :: acc)

# A comment on its own line belongs with the next line if it is indented at
# least as far, else with the block its column is in.
fn resolve placed next acc -> r : placed~List Placed, next~Option (Nat, Nat), acc~List Placed, r~List Placed
    match placed
        []        -> acc
        p :: rest ->
            match (starts p.role, p.role)
                (Some lvl, _)  ->
                    let col = match p.line.toks
                        []     -> 0
                        t :: _ -> t.col
                    resolve rest (Some (col, lvl)) (p :: acc)
                (_, Note back) ->
                    let col = match p.line.comment
                        Some c -> c.col
                        None   -> 0
                    let lvl = match next
                        Some (c, l) -> if col >= c then l else back
                        None        -> back
                    resolve rest next (Placed (Note lvl) p.line :: acc)
                _              -> resolve rest next (p :: acc)

# The lines of a file, each with its role.
export fn layout lines -> r : lines~List Line, r~Result (List Placed) SyntaxError
    let placed = try place lines (State [(0, False)] 0 None 0 0 0 False) []
    Ok (resolve (reverse placed) None [])

# ── Indentation for a new line (D158) ───────────────────────────────────────

# One indentation level.
let LEVEL = 4

# An open bracket: the column its logical line starts at, the column of the
# first token after it on its line, if any, and whether that token may still
# come (the bracket was opened on the line being read).
record Open
    base~Nat
    content~Option Nat
    waiting~Bool

# The brackets open after `toks` (innermost first), on a logical line
# starting at column `base`.
fn opens toks base stack -> r : toks~List Tok, base~Nat, stack~List Open, r~List Open
    match toks
        []        -> stack
        t :: rest ->
            let filled = match stack
                o :: more if o.waiting and not (is_close t) -> Open o.base (Some t.col) False :: more
                _ -> stack
            if is_open t
                opens rest base (Open base None True :: filled)
            else if is_close t
                match filled
                    _ :: more -> opens rest base more
                    []        -> opens rest base []
            else
                opens rest base filled

# At the end of a physical line, a bracket with nothing after it waits no
# more: its continuation lines go one level in from its line.
fn settled stack -> r : stack~List Open, r~List Open
    list.map (\o -> Open o.base o.content False) stack

fn lines_opens lines base stack -> r : lines~List Line, base~Nat, stack~List Open, r~List Open
    match lines
        []        -> stack
        l :: rest -> lines_opens rest base (settled (opens l.toks base stack))

fn words_of toks -> r : toks~List Tok, r~List Bytes
    list.map (\t -> t.text) toks

# Does the logical line open a block on the next line? It ends with `->`
# or `=`, or it is a declaration, `match`, `if` without `then`, `else`, or
# `when` header (§9.2).
fn opens_block toks -> b : toks~List Tok, b~Bool
    let ws = words_of toks
    let last = match last_of toks
        Some t -> t.text
        None   -> b""
    let first = match toks
        t :: _ -> t.text
        []     -> b""
    let decl = any_head (list.take 4 ws)
    if last == b"->" or last == b"="
        True
    else if decl and not (list.contains ws b"=" and first == b"type")
        True
    else if first == b"if" or (first == b"else" and list.contains ws b"if")
        not (list.contains ws b"then")
    else if first == b"else"
        True
    else
        first == b"match" or first == b"when"

let HEADS = [b"fn", b"enum", b"record", b"lemma", b"class", b"instance", b"proof"]

fn any_head ws : ws~List Bytes
    match ws
        []        -> False
        w :: rest -> list.contains HEADS w or any_head rest

# The code lines of the last logical line in `placed`, in order.
fn last_logical placed acc -> r : placed~List Placed, acc~List Line, r~List Line
    match placed
        []        -> acc
        p :: rest ->
            match (starts p.role, p.role)
                (Some _, _) -> p.line :: acc
                (_, Cont)   -> if p.line.toks == [] then last_logical rest acc else last_logical rest (p.line :: acc)
                _           -> if acc == [] then last_logical rest acc else acc

fn last_line lines -> r : lines~List Line, r~Option Line
    match lines
        []        -> None
        [l]       -> Some l
        _ :: rest -> last_line rest

fn first_col toks -> c : toks~List Tok, c~Nat
    match toks
        t :: _ -> t.col
        []     -> 0

fn all_toks lines -> r : lines~List Line, r~List Tok
    match lines
        []        -> []
        l :: rest -> l.toks ++ all_toks rest

# The column a new line should start at, after `lines` (the lines before it),
# when its first token is `first`: inside brackets, aligned with what follows
# the innermost one, or one level in from its line; after a line that opens
# a block or doesn't end, one level in; else at the level of the line before.
export fn indent_after lines first -> c : lines~List Line, first~Option Tok, c~Nat
    match layout lines
        Err _     -> 0
        Ok placed ->
            match last_logical (reverse placed) []
                []            -> 0
                start :: more ->
                    let base = match start.toks
                        t :: _ -> t.col
                        []     -> 0
                    let logical = start :: more
                    let stack = lines_opens logical base []
                    let closing = match first
                        Some t -> is_close t
                        None   -> False
                    match stack
                        o :: _ ->
                            if closing
                                o.base
                            else
                                match o.content
                                    Some c -> c
                                    None   -> o.base + LEVEL
                        []     ->
                            let toks = all_toks logical
                            let ends_open = match last_of toks
                                Some t -> (is_binop t and not (is_punct t b".")) or is_punct t b","
                                None   -> False
                            # A continuation line that opens a block (a `match`
                            # among a signature's constraints): one level in from it.
                            let continued = match (more, last_line more)
                                (_ :: _, Some l) -> if opens_block l.toks then Some (first_col l.toks) else None
                                _                -> None
                            match continued
                                Some c if not ends_open -> c + LEVEL
                                _ -> if ends_open or opens_block toks then base + LEVEL else base
