# ck/format.ck — the formatter (D91, D92, SPEC §15.4): one style, no
# options. It keeps the author's line breaks, comments and literals, and
# normalizes indentation, spacing, alignment and blank lines.

module ck.format

import bytes
import list (reverse)
import list
import ck.syntax as syntax
import ck.syntax (Tok, Line, Placed, Role, Kind, SyntaxError, Name, Upper, Number, Literal, Punct, Comment,
                  Blank, Start, Cont, Note)

export let INDENT = 4

# ── Spacing ──────────────────────────────────────────────────────────────────

# A token that ends an operand: after it, `-` is subtraction, and a glued
# `.` or `[` is field access or indexing (D22).
fn operand_end t : t~Tok
    match t.kind
        Name -> not (syntax.is_keyword t)
        Upper -> True
        Number -> True
        Literal -> True
        Punct -> syntax.is_close t
        Comment -> False

fn is_number t : t~Tok
    match t.kind
        Number -> True
        _ -> False

# What the previous token was, for spacing.
enum After
    Begin                      # nothing yet: the start of the logical line
    Token t : t~Tok
    Unary                      # a unary minus
    Field                      # a glued `.`

fn is_unary prev t next pattern : prev~After, t~Tok, next~Option Tok, pattern~Bool
    syntax.is_punct t b"-" and unary_after prev next pattern

# A `-` here is a sign: nothing it could subtract from comes before it, or
# it is in a pattern, before a number (`Num -1 ->`).
fn unary_after prev next pattern : prev~After, next~Option Tok, pattern~Bool
    match prev
        Token p -> not (operand_end p) or (pattern and next_is_number next)
        _ -> True

fn field_dot prev t : prev~After, t~Tok
    match prev
        Token p -> syntax.is_punct t b"." and glued_postfix p t
        _ -> False

fn no_brackets bs : bs~List Bracket
    match bs
        [] -> True
        _ -> False

fn next_is_number next : next~Option Tok
    match next
        Some n -> is_number n
        None -> False

# Spaces between `prev` and `t` on one line.
fn gap prev t -> n : prev~After, t~Tok, n~Nat
    match prev
        Begin -> 0
        Unary -> 0
        Field -> 0
        Token p ->
            if syntax.is_punct t b"," or syntax.is_punct p b"(" or syntax.is_punct p b"["
                0
            else if syntax.is_punct t b")" or syntax.is_punct t b"]"
                0
            else if syntax.is_punct p b"{" and syntax.is_punct t b"}"
                0
            else if syntax.is_punct t b"~" or syntax.is_punct p b"~" or syntax.is_punct p b"\\"
                0
            else if glued_postfix p t
                0
            else
                1

# A glued `.` or `[` after an operand: field access or indexing (D22).
fn glued_postfix p t : p~Tok, t~Tok
    (syntax.is_punct t b"." or syntax.is_punct t b"[") and not t.spaced and operand_end p

# ── Rendering one logical line ───────────────────────────────────────────────

# An open bracket: the column of the first token after it on its line (if
# any yet), and the column its line starts at.
record Bracket
    content~Option Nat
    base~Nat

# Rendering state within a logical line.
record Cursor
    col~Nat
    prev~After
    brackets~List Bracket      # innermost first
    sig~Option Nat             # where a signature's constraints start
    sig_wait~Bool              # a signature's `:` was the last token
    pattern~Bool               # before a match arm's `->`
    header~Bool                # a type's parameters, where `+v` and `-v` are polarities (D16)

fn spaces n -> b : n~Nat, b~Bytes
    decreasing n
    if n == 0 then b"" else b" " ++ spaces (n - 1)

# Fill in the content column of a bracket waiting for its first token.
fn fill brackets col -> r : brackets~List Bracket, col~Nat, r~List Bracket
    match brackets
        b :: rest ->
            match b.content
                None -> Bracket (Some col) b.base :: rest
                Some _ -> brackets
        [] -> []

# At the end of a physical line, a bracket with nothing after it puts its
# continuation lines one level in from its line.
fn settle brackets -> r : brackets~List Bracket, r~List Bracket
    match brackets
        [] -> []
        b :: rest ->
            match b.content
                None -> Bracket (Some (b.base + INDENT)) b.base :: settle rest
                Some _ -> b :: settle rest

fn pop brackets -> r : brackets~List Bracket, r~List Bracket
    match brackets
        [] -> []
        _ :: rest -> rest

# Emit the tokens of one physical line. `target`: the column the aligned
# token (`->` of an arm, `:` of a constructor) starts at; `base`: the
# column this physical line starts at.
fn emit toks cur target what base lead acc -> r : toks~List Tok, cur~Cursor, target~Option Nat, what~Bytes,
                                                  base~Nat, lead~Bool, acc~List Bytes, r~(List Bytes, Cursor)
    match toks
        [] -> (reverse acc, Cursor cur.col cur.prev (settle cur.brackets) cur.sig cur.sig_wait cur.pattern cur.header)
        t :: rest ->
            let next = match rest
                [] -> None
                n :: _ -> Some n
            let top = no_brackets cur.brackets
            let aligned = top and syntax.is_punct t what
            let normal = if lead then 0 else gap cur.prev t
            let n = match target
                Some c -> if aligned then (if c > cur.col + 1 then c - cur.col else 1) else normal
                None -> normal
            let col = cur.col + n
            let brackets = fill cur.brackets col
            let polarity = cur.header and (syntax.is_punct t b"+" or syntax.is_punct t b"-")
            let unary = polarity or is_unary cur.prev t next cur.pattern
            let field = field_dot cur.prev t
            let prev = if unary then Unary else if field then Field else Token t
            let brackets2 = if syntax.is_open t
                Bracket None base :: brackets
            else if syntax.is_close t
                pop brackets
            else
                brackets
            let sig = if cur.sig_wait then Some col else cur.sig
            let sig_wait = cur.sig == None and not cur.sig_wait and top and syntax.is_punct t b":"
            let pattern = cur.pattern and not (top and syntax.is_punct t b"->")
            let target2 = if aligned then None else target
            let header = cur.header and not (top and (syntax.is_punct t b":" or syntax.is_punct t b"="))
            let c2 = Cursor (col + t.wide) prev brackets2 sig sig_wait pattern header
            emit rest c2 target2 what base False (t.text :: spaces n :: acc)

# Where a continuation line starts (D92).
fn cont_col cur first indent -> c : cur~Cursor, first~Option Tok, indent~Nat, c~Nat
    match cur.brackets
        b :: _ ->
            let closing = match first
                Some t -> syntax.is_close t
                None -> False
            if closing
                b.base
            else
                match b.content
                    Some c -> c
                    None -> b.base + INDENT
        [] ->
            match cur.sig
                Some c -> c
                None -> indent + INDENT

# ── Alignment (D92) ──────────────────────────────────────────────────────────

# What a block's lines align: the `->` of match arms, the `:` of enum
# constructors, or nothing.
enum Block
    Arms
    Ctors
    Plain

fn skip_modifiers toks -> r : toks~List Tok, r~List Tok
    match toks
        t :: rest ->
            if syntax.is_text t b"export" or syntax.is_text t b"abstract" or syntax.is_text t b"transparent"
                skip_modifiers rest
            else
                toks
        [] -> []

fn has_match toks d : toks~List Tok, d~Nat
    match toks
        [] -> False
        t :: rest ->
            if d == 0 and syntax.is_text t b"match" and syntax.is_keyword t
                True
            else
                has_match rest (syntax.depth_after [t] d)

fn block_of toks -> b : toks~List Tok, b~Block
    if has_match toks 0
        Arms
    else
        match skip_modifiers toks
            t :: _ -> if syntax.is_text t b"enum" then Ctors else Plain
            [] -> Plain

fn aligns b -> r : b~Block, r~Option Bytes
    match b
        Arms -> Some b"->"
        Ctors -> Some b":"
        Plain -> None

# The tokens before the first `what` outside brackets, if there is one.
fn before toks what d acc -> r : toks~List Tok, what~Bytes, d~Nat, acc~List Tok, r~Option (List Tok)
    match toks
        [] -> None
        t :: rest ->
            if d == 0 and syntax.is_punct t what
                Some (reverse acc)
            else
                before rest what (syntax.depth_after [t] d) (t :: acc)

fn fresh col pattern header -> c : col~Nat, pattern~Bool, header~Bool, c~Cursor
    Cursor col Begin [] None False pattern header

# A type declaration's first line: its parameters may have polarities.
fn type_header toks : toks~List Tok
    match skip_modifiers toks
        t :: _ -> syntax.is_text t b"record" or syntax.is_text t b"enum"
        [] -> False

# The width of tokens rendered from column 0.
fn rendered_width toks pattern -> w : toks~List Tok, pattern~Bool, w~Nat
    let (_, cur) = emit toks (fresh 0 pattern False) None b"" 0 True []
    cur.col

record Frame
    lvl~Nat
    id~Nat
    block~Block

# One logical line's alignment: its run (the block it is in, and the blank
# lines seen so far) and the width before its aligned token.
record Entry
    parent~Nat
    blanks~Nat
    width~Option Nat
    what~Bytes

fn pop_frames frames lvl -> r : frames~List Frame, lvl~Nat, r~List Frame
    match frames
        f :: rest -> if f.lvl >= lvl then pop_frames rest lvl else frames
        [] -> []

fn entries placed frames next blanks acc -> r : placed~List Placed, frames~List Frame, next~Nat, blanks~Nat,
                                                acc~List Entry, r~List Entry
    match placed
        [] -> reverse acc
        p :: rest ->
            match p.role
                Blank -> entries rest frames next (blanks + 1) acc
                Start lvl ->
                    let fs = pop_frames frames lvl
                    let (parent, block) = match fs
                        f :: _ -> if f.lvl + 1 == lvl then (f.id, f.block) else (next, Plain)
                        [] -> (next, Plain)
                    let toks = p.line.toks
                    let e = match aligns block
                        Some what ->
                            match before toks what 0 []
                                Some pre -> Entry parent blanks (Some (rendered_width pre (block == Arms))) what
                                None -> Entry parent blanks None what
                        None -> Entry parent blanks None b""
                    entries rest (Frame lvl next (block_of toks) :: fs) (next + 1) blanks (e :: acc)
                _ -> entries rest frames next blanks acc

fn run_max es parent blanks m -> r : es~List Entry, parent~Nat, blanks~Nat, m~Nat, r~Nat
    match es
        [] -> m
        e :: rest ->
            let w = match e.width
                Some w -> if e.parent == parent and e.blanks == blanks and w > m then w else m
                None -> m
            run_max rest parent blanks w

# For each logical line, the column (from its indentation) its aligned
# token starts at, and that token.
fn targets es all -> r : es~List Entry, all~List Entry, r~List (Option Nat, Bytes)
    match es
        [] -> []
        e :: rest ->
            let t = match e.width
                Some _ -> Some (run_max all e.parent e.blanks 0 + 1)
                None -> None
            (t, e.what) :: targets rest all

# ── Blank lines ──────────────────────────────────────────────────────────────

fn level_of p cur -> l : p~Placed, cur~Nat, l~Nat
    match p.role
        Start l -> l
        Note l -> l
        _ -> cur

# Keep a blank line only between two non-blank lines, once, and not just
# before a line deeper than the one before it (the start of a block).
fn blanks placed prev pending acc -> r : placed~List Placed, prev~Option Nat, pending~Bool, acc~List Placed,
                                         r~List Placed
    match placed
        [] -> reverse (if pending then drop_blank acc else acc)
        p :: rest ->
            match p.role
                Blank -> blanks rest prev True (if pending then acc else p :: acc)
                _ ->
                    let l = level_of p (or_zero prev)
                    let keep = pending and not_deeper prev l
                    let acc2 = if pending and not keep then drop_blank acc else acc
                    blanks rest (Some l) False (p :: acc2)

fn or_zero o -> n : o~Option Nat, n~Nat
    match o
        Some n -> n
        None -> 0

fn not_deeper prev l : prev~Option Nat, l~Nat
    match prev
        Some q -> l <= q
        None -> False

fn drop_blank acc -> r : acc~List Placed, r~List Placed
    match acc
        p :: rest ->
            match p.role
                Blank -> rest
                _ -> acc
        [] -> []

# ── Output ───────────────────────────────────────────────────────────────────

enum Out
    Gap
    Alone text : text~Bytes                                  # a comment on its own line
    Code text width comment gap : text~Bytes, width~Nat, comment~Option Tok, gap~Nat

# Render the lines, each logical line with its alignment target.
fn render placed ts lvl cur acc -> r : placed~List Placed, ts~List (Option Nat, Bytes), lvl~Nat, cur~Cursor,
                                       acc~List Out, r~List Out
    match placed
        [] -> reverse acc
        p :: rest ->
            let l = p.line
            match p.role
                Blank -> render rest ts lvl cur (Gap :: acc)
                Note n ->
                    let text = spaces (n * INDENT) ++ comment_text l.comment
                    render rest ts lvl cur (Alone text :: acc)
                Start n ->
                    let (target, what, ts2) = match ts
                        (t, w) :: more -> (t, w, more)
                        [] -> (None, b"", [])
                    let indent = n * INDENT
                    let abs = match target
                        Some t -> Some (indent + t)
                        None -> None
                    let arm = what == b"->"
                    let (pieces, c2) = emit l.toks (fresh indent arm (type_header l.toks)) abs what indent True []
                    let text = spaces indent ++ bytes.concat pieces
                    render rest ts2 n c2 (Code text c2.col l.comment (author_gap l) :: acc)
                Cont ->
                    let first = match l.toks
                        t :: _ -> Some t
                        [] -> None
                    let col = cont_col cur first (lvl * INDENT)
                    match l.toks
                        [] -> render rest ts lvl cur (Alone (spaces col ++ comment_text l.comment) :: acc)
                        _ ->
                            let start = Cursor col cur.prev cur.brackets cur.sig cur.sig_wait False cur.header
                            let (pieces, c2) = emit l.toks start None b"" col True []
                            let text = spaces col ++ bytes.concat pieces
                            render rest ts lvl c2 (Code text c2.col l.comment (author_gap l) :: acc)

# The spaces between a line's code and its comment, as written.
fn author_gap l -> g : l~Line, g~Nat
    match l.comment
        None -> 0
        Some c -> gap_after l.toks c.col

fn gap_after toks col -> g : toks~List Tok, col~Nat, g~Nat
    match toks
        [] -> 0
        [t] -> if col > t.col + t.wide then col - (t.col + t.wide) else 0
        _ :: rest -> gap_after rest col

fn comment_text c -> b : c~Option Tok, b~Bytes
    match c
        Some t -> t.text
        None -> b""

# Trailing comments on consecutive lines start in one column: the furthest
# of each line's code end plus the spaces its author put before the comment
# (at least two). So aligned comments stay aligned as the code moves.
fn comment_col outs c -> r : outs~List Out, c~Nat, r~Nat
    match outs
        (Code _ w (Some t) gap) :: rest ->
            let need = w + (if gap > 2 then gap else 2)
            comment_col rest (if need > c then need else c)
        _ -> c

fn finish outs run acc -> r : outs~List Out, run~Option Nat, acc~List Bytes, r~List Bytes
    match outs
        [] -> reverse acc
        o :: rest ->
            match o
                Gap -> finish rest None (b"" :: acc)
                Alone text -> finish rest None (text :: acc)
                Code text w None _ -> finish rest None (text :: acc)
                Code text w (Some t) _ ->
                    let c = match run
                        Some c -> c
                        None -> comment_col outs 0
                    let pad = if c > w then c - w else 2
                    finish rest (Some c) ((text ++ spaces pad ++ t.text) :: acc)

fn lines_text ls -> b : ls~List Bytes, b~Bytes
    match ls
        [] -> b""
        _ -> bytes.concat (newlines ls [])

fn newlines ls acc -> r : ls~List Bytes, acc~List Bytes, r~List Bytes
    match ls
        [] -> reverse acc
        l :: rest -> newlines rest (b"\n" :: l :: acc)

# Format a file: its text in the one style, or why it can't be read.
export fn format src -> r : src~Bytes, r~Result Bytes SyntaxError
    let lines = try syntax.lex src
    let placed = try syntax.layout lines
    let kept = blanks placed None False []
    let es = entries kept [] 0 0 []
    let outs = render kept (targets es es) 0 (fresh 0 False False) []
    Ok (lines_text (finish outs None []))
