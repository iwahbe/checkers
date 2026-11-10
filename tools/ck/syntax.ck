# ck/syntax.ck — Checkers source as tokens and lines, keeping comments and
# blank lines (D93). The lexer follows SPEC §9.1; the layout pass assigns
# each line its block level, or marks it as continuing the line before.

module ck.syntax

import bytes
import list (reverse)
import list

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
        or two src i e '<' '-' or two src i e '<' '=' or two src i e '>' '=' or two src i e '-' '>'

fn one_char c : c~U8
    c == '+' or c == '-' or c == '*' or c == '/' or c == '%' or c == '<' or c == '>'
        or c == '$' or c == '.' or c == '(' or c == ')' or c == '[' or c == ']'
        or c == '{' or c == '}' or c == ',' or c == ':' or c == '~' or c == '\\'
        or c == '|' or c == '='

# One token starting at `i` (not a space or a comment).
fn scan src i e n col -> r : src~Bytes, i~Nat, e~Nat, i < e, e <= len src, n~Nat, col~Nat,
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
                    let s = try scan src i e n col
                    let w = width src i s.stop
                    let t = Tok s.kind (bytes.slice src i s.stop) col w spaced
                    lex_line src ls s.stop e n (col + w) (t :: acc)

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

let KEYWORDS = [b"module", b"import", b"as", b"export", b"abstract", b"transparent", b"fn", b"enum",
                b"record", b"type", b"let", b"lemma", b"ensures", b"proof", b"have", b"auto", b"admit",
                b"check", b"match", b"if", b"then", b"else", b"try", b"decreasing", b"partial",
                b"ghost", b"own", b"comptime", b"when", b"using", b"par"]

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
# level of the line it belongs with.
export enum Role
    Blank
    Start lvl : lvl~Nat
    Cont
    Note lvl  : lvl~Nat

export record Placed
    role~Role
    line~Line

# Layout state: the columns of the open blocks (innermost first), the
# bracket depth, and the last code token so far.
record State
    stack~List Nat
    depth~Nat
    last~Option Tok

fn last_of toks -> r : toks~List Tok, r~Option Tok
    match toks
        []        -> None
        [t]       -> Some t
        _ :: rest -> last_of rest

# The last line ends with a binary operator or a comma.
fn open_ended st : st~State
    match st.last
        Some t -> is_binop t or is_punct t b","
        None   -> False

fn continues st first : st~State, first~Tok
    st.depth > 0 or is_binop first or is_punct first b":" or open_ended st

# The level of the innermost open block whose column is at most `col`.
fn level_at stack col -> l : stack~List Nat, col~Nat, l~Nat
    match stack
        []        -> 0
        c :: rest -> if c <= col then list.length rest else level_at rest col

# Close blocks down to `col`: the remaining stack, if `col` is one of its
# columns.
fn dedent stack col -> r : stack~List Nat, col~Nat, r~Option (List Nat)
    match stack
        []        -> None
        c :: rest -> if c == col then Some stack else if c < col then None else dedent rest col

# The level of the innermost block.
fn level_of stack -> l : stack~List Nat, l~Nat
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
                            let role = if st.depth > 0 or open_ended st then Cont else Note (level_at st.stack c.col)
                            place rest st (Placed role l :: acc)
                first :: _ ->
                    let next = State st.stack (depth_after l.toks st.depth) (last_of l.toks)
                    if st.last != None and continues st first
                        place rest next (Placed Cont l :: acc)
                    else
                        let top = match st.stack
                            []     -> 0
                            c :: _ -> c
                        if first.col > top
                            if st.last == None
                                Err (error l.num first.col "unexpected indentation at the start of the file")
                            else
                                let stack = first.col :: st.stack
                                let p = Placed (Start (list.length st.stack)) l
                                place rest (State stack next.depth next.last) (p :: acc)
                        else
                            match dedent st.stack first.col
                                None       -> Err (error l.num first.col "unindent does not match any outer indentation level")
                                Some stack ->
                                    let p = Placed (Start (level_of stack)) l
                                    place rest (State stack next.depth next.last) (p :: acc)

# A comment on its own line belongs with the next line if it is indented at
# least as far, else with the block its column is in.
fn resolve placed next acc -> r : placed~List Placed, next~Option (Nat, Nat), acc~List Placed, r~List Placed
    match placed
        []        -> acc
        p :: rest ->
            match p.role
                Start lvl ->
                    let col = match p.line.toks
                        []     -> 0
                        t :: _ -> t.col
                    resolve rest (Some (col, lvl)) (p :: acc)
                Note back ->
                    let col = match p.line.comment
                        Some c -> c.col
                        None   -> 0
                    let lvl = match next
                        Some (c, l) -> if col >= c then l else back
                        None        -> back
                    resolve rest next (Placed (Note lvl) p.line :: acc)
                _         -> resolve rest next (p :: acc)

# The lines of a file, each with its role.
export fn layout lines -> r : lines~List Line, r~Result (List Placed) SyntaxError
    let placed = try place lines (State [0] 0 None) []
    Ok (resolve (reverse placed) None [])
