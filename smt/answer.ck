# answer.ck — Z3's answer to a query, as the corpus keeps it (SPEC §7.2),
# and the model its `(get-value …)` output describes.
#
# A corpus answer is `;; work N`, then `sat`, `unsat` or `unknown`, then,
# after `sat` when the query asks `(get-value (t1 … tn))`, one list
# `((t1 v1) … (tn vn))`. Z3 prints values for those terms only: the
# queries `ckc` writes ask for the constants the user named, so Z3 prints
# nothing for `ckc`'s own constants (`$x#0`), for functions with
# parameters, for division by zero, for `seq.nth` out of range, for a
# selector applied to another constructor's value, or for the size of an
# uninterpreted sort.
#
# Nor does Z3 print a universe for an uninterpreted sort, so how many
# elements one has is not known from the values: in the model they make,
# such a sort is `Unsized`, and whatever depends on its size is not
# determined.
#
# `printed` reads the values: each one is checked whole against the sort
# of the term asked (`printed.checked`), and every pair must agree with
# the model the pairs make: a term printed twice with two values, or a
# value that isn't what the other values make its term, is not read. `model_of` makes them a `Model`
# that says only what was printed and answers `None` everywhere else, so
# that a term needing anything else evaluates to `NotGiven`.

module answer

import std.list
import std.bytes
import smtlib
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node, Shape)
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, SortDecl, Sig, Context)
import term (Head, Fun, Prim, Sel, Term, App, Op, Div, Mod, SeqNth)
import model (Value, Truth, Integer, Sequence, Constructed, Element, Model, Domain, Unsized)
import printed
import printed (Names, Defs)

# What Z3 answered: its first word after the work line.
export enum Verdict
    Sat
    Unsat
    GaveUp
    Other

# The verdict of an answer's text: its first line that isn't a comment.
export fn verdict text -> v : text~Bytes, v~Verdict
    first_word text 0

fn first_word text i -> v : text~Bytes, i~Nat, i <= len text, v~Verdict
    decreasing len text - i
    let j = line_end text i
    let line = bytes.slice text i j
    if j >= len text and i >= len text
        Other
    else if len line > 0 and line[0] == ';'
        if j < len text then first_word text (j + 1) else Other
    else if line == b"sat"
        Sat
    else if line == b"unsat"
        Unsat
    else if line == b"unknown"
        GaveUp
    else
        Other

fn line_end text i -> j : text~Bytes, i~Nat, i <= len text, j~Nat, i <= j, j <= len text
    decreasing len text - i
    if i < len text and text[i] != '\n' then line_end text (i + 1) else i

# An answer's text without the line Z3 prints for `(get-unsat-core)` after
# `sat`: exactly `(error "line L column C: unsat core is not available")`,
# alone on the line right after `sat`. Nothing else is removed: any other
# error, or this one anywhere else, stays and fails to read.
export fn without_core_error text -> r : text~Bytes, r~Bytes
    let i = after_comments text 0
    let j = line_end text i
    if bytes.slice text i j == b"sat" and j < len text
        let k = line_end text (j + 1)
        if core_line (bytes.slice text (j + 1) k)
            bytes.slice text 0 (j + 1) ++ (if k < len text then bytes.slice text (k + 1) (len text) else b"")
        else
            text
    else
        text

# Where the first line that isn't a comment starts.
fn after_comments text i -> r : text~Bytes, i~Nat, i <= len text, r~Nat, r <= len text
    decreasing len text - i
    let j = line_end text i
    if i < len text and text[i] == ';' and j < len text then after_comments text (j + 1) else i

fn core_line line -> r : line~Bytes, r~Bool
    let head = b"(error \"line "
    let middle = b" column "
    let tail = b": unsat core is not available\")"
    if len line > len head and bytes.matches_at line 0 head
        let a = digits_end line (len head)
        if a > len head and a + len middle <= len line and bytes.matches_at line a middle
            let b = digits_end line (a + len middle)
            b > a + len middle and b + len tail == len line and bytes.matches_at line b tail
        else
            False
    else
        False

# Where the digits from `i` end.
fn digits_end line i -> r : line~Bytes, i~Nat, i <= len line, r~Nat, r >= i, r <= len line
    decreasing len line - i
    if i < len line and line[i] >= '0' and line[i] <= '9' then digits_end line (i + 1) else i

# ── Values ───────────────────────────────────────────────────────────────────

# The `(get-value …)` terms of a query, as written: what `get-value` in
# `es`, the query's S-expressions, asks for.
export fn asked es -> r : es~List (SExpr src), r~List Shape
    match es
        []        -> []
        e :: rest ->
            match e
                Node [Leaf (Symbol g False) _, Node ts _] _ if g == b"get-value" -> smtlib.shapes ts
                _ -> asked rest

# What the values say, before a model is made of them: nothing of the
# query's own beyond its declarations.
fn bare c -> n : c~Context, n~Names
    Names (term.signature c) [] []

fn no_defs c -> d : c~Context, d~Defs
    Defs (term.signature c) (\_ _ -> Unsized) []

# The value `e` writes, as a value of sort `s` in `c`.
export fn value_of c s e -> r : c~Context, s~Sort, e~SExpr src, r~Result Value Bytes
    let t = try printed.checked (bare c) [] s e
    printed.eval (no_defs c) 0 [] t

# The values printed for `terms` (in order, written `written` in the query)
# in an answer whose S-expressions are `es`: `sat`, then the one
# `(get-value …)` list, and nothing else.
export fn printed c terms written es -> r : c~Context, terms~List Term, written~List Shape, es~List (SExpr src),
                                            r~Result (List (Term, Value)) Bytes
    match es
        [Leaf (Symbol v False) _, vals] if v == b"sat" -> values_list c terms written vals
        _ -> Err b"not `sat` and one `(get-value …)` list"

# The `(get-value …)` list `e` for `terms`: each printed term the one asked
# there, written the same way, with a value of its sort; and the pairs
# agree with each other (`agree`).
export fn values_list c terms written e -> r : c~Context, terms~List Term, written~List Shape, e~SExpr src,
                                               r~Result (List (Term, Value)) Bytes
    match e
        Node pairs _ ->
            let ps = try pair_values c terms written pairs
            if agree c ps (model_of c ps 0) then Ok ps else Err b"values printed that contradict each other"
        _            -> Err b"a `(get-value …)` answer that isn't a list"

fn pair_values c terms written pairs -> r : c~Context, terms~List Term, written~List Shape, pairs~List (SExpr src),
                                            r~Result (List (Term, Value)) Bytes
    let sig = term.signature c
    match (terms, written, pairs)
        ([], [], [])                            -> Ok []
        (t :: tr, w :: wr, Node [p, e] _ :: pr) ->
            if smtlib.same sig w (smtlib.shape p)
                match term.sort_of sig [] t
                    Ok s  ->
                        let v = try value_of c s e
                        let more = try pair_values c tr wr pr
                        Ok ((t, v) :: more)
                    Err _ -> Err b"a `get-value` term without a sort"
            else
                Err b"a printed value for a term other than the one asked for there"
        _                                       -> Err b"the values printed don't match the terms asked for"

# Whether each printed value is what its term evaluates to in `m`, where
# `m` says what the term is (a term `m` doesn't determine is not compared:
# it holds no contradiction).
export fn agree c ps m -> r : c~Context, ps~List (Term, Value), m~Model, r~Bool
    match ps
        []             -> True
        (t, v) :: rest ->
            match model.eval c m t
                Ok w  -> w == v and agree c rest m
                Err _ -> agree c rest m

# Whether each printed value is what its term evaluates to in `m`, a
# model printed beside the values: there every term must be determined.
export fn given_by c ps m -> r : c~Context, ps~List (Term, Value), m~Model, r~Bool
    match ps
        []             -> True
        (t, v) :: rest -> model.eval c m t == Ok v and given_by c rest m

# ── The model ────────────────────────────────────────────────────────────────

# What one printed value says about the model.
enum Says
    FunAt f vs v         : f~Nat, vs~List Value, v~Value
    DivAt n v            : n~Int, v~Int
    ModAt n v            : n~Int, v~Int
    NthAt e xs i v       : e~Sort, xs~List Value, i~Int, v~Value
    SelAt d k j args x v : d~Nat, k~Nat, j~Nat, args~List Sort, x~Value, v~Value
    Nothing

# The model that knows nothing: every question is `NotGiven`, except what
# `normal_arrays` computes, and no uninterpreted sort's size is known.
export fn empty_model sig fuel -> m : sig~Sig, fuel~Nat, m~Model
    let none5 = \_ _ _ _ _ -> None
    model.normal_arrays sig (model.without_arrays (\_ _ -> None) (\_ -> None) (\_ -> None) (\_ _ _ -> None) none5 (\_ _ -> Unsized) fuel)

fn known c fuel ts -> r : c~Context, fuel~Nat, ts~List Term, r~Option (List Value)
    match ts
        []        -> Some []
        t :: rest ->
            match (model.eval c (empty_model (term.signature c) fuel) t, known c fuel rest)
                (Ok v, Some vs) -> Some (v :: vs)
                _               -> None

# What `t` printed as `v` says: a function's value at arguments that are
# values by themselves, `div` or `mod` by zero, `seq.nth` out of range, or
# a selector applied to another constructor's value.
fn says c fuel t v -> r : c~Context, fuel~Nat, t~Term, v~Value, r~Says
    match t
        App (Fun f) args         ->
            match known c fuel args
                Some vs -> FunAt f vs v
                None    -> Nothing
        App (Prim Div) [a, b]    ->
            match (known c fuel [a, b], v)
                (Some [Integer n, Integer 0], Integer w) -> DivAt n w
                _                                        -> Nothing
        App (Prim Mod) [a, b]    ->
            match (known c fuel [a, b], v)
                (Some [Integer n, Integer 0], Integer w) -> ModAt n w
                _                                        -> Nothing
        App (Prim SeqNth) [a, b] ->
            match (known c fuel [a, b], term.sort_of (term.signature c) [] t)
                (Some [Sequence xs, Integer i], Ok e) ->
                    if 0 <= i and i < list.length xs then Nothing else NthAt e xs i v
                _                                     -> Nothing
        App (Sel d k j) [a]      ->
            match (known c fuel [a], term.sort_of (term.signature c) [] a)
                (Some [Constructed l fs], Ok (Data _ args)) ->
                    if l == k then Nothing else SelAt d k j args (Constructed l fs) v
                _                                           -> Nothing
        _                        -> Nothing

fn fun_at ss f vs -> r : ss~List Says, f~Nat, vs~List Value, r~Option Value
    match ss
        FunAt g ws v :: rest -> if g == f and ws == vs then Some v else fun_at rest f vs
        _ :: rest            -> fun_at rest f vs
        []                   -> None

fn div_at ss n -> r : ss~List Says, n~Int, r~Option Int
    match ss
        DivAt m v :: rest -> if m == n then Some v else div_at rest n
        _ :: rest         -> div_at rest n
        []                -> None

fn mod_at ss n -> r : ss~List Says, n~Int, r~Option Int
    match ss
        ModAt m v :: rest -> if m == n then Some v else mod_at rest n
        _ :: rest         -> mod_at rest n
        []                -> None

fn nth_at ss e xs i -> r : ss~List Says, e~Sort, xs~List Value, i~Int, r~Option Value
    match ss
        NthAt f ys j v :: rest -> if f == e and ys == xs and j == i then Some v else nth_at rest e xs i
        _ :: rest              -> nth_at rest e xs i
        []                     -> None

fn sel_at ss d k j args x -> r : ss~List Says, d~Nat, k~Nat, j~Nat, args~List Sort, x~Value, r~Option Value
    match ss
        SelAt d2 k2 j2 a2 x2 v :: rest ->
            if d2 == d and k2 == k and j2 == j and a2 == args and x2 == x then Some v else sel_at rest d k j args x
        _ :: rest                      -> sel_at rest d k j args x
        []                             -> None

# The model that says exactly what was printed (`pairs`), and nothing else:
# no uninterpreted sort's size is known (`Unsized`), and it may go `fuel`
# levels deep.
export fn model_of c pairs fuel -> m : c~Context, pairs~List (Term, Value), fuel~Nat, m~Model
    let ss = list.map (\(t, v) -> says c fuel t v) pairs
    let funs = \f vs -> fun_at ss f vs
    let nth = \e xs i -> nth_at ss e xs i
    let sel = \d k j args x -> sel_at ss d k j args x
    model.normal_arrays (term.signature c) (model.without_arrays funs (\n -> div_at ss n) (\n -> mod_at ss n) nth sel (\_ _ -> Unsized) fuel)
