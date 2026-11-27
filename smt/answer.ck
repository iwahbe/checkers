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
# determined. (Beside a model, the universes it prints are used.)
#
# `printed` reads the values: each one is checked whole against the sort
# of the term asked (`printed.checked`). The pairs make one model
# (`model_of`): a constant's pair gives its value, and a declared
# function's pair gives its value at arguments the other pairs give
# values to (`x` before `(f x)`), as do `div` or `mod` by zero, `seq.nth`
# out of range and a selector of another constructor's value. Then every
# pair's term must have its printed value in that model, the query's
# definitions run as their bodies: a term printed twice with two values,
# a value the other values or the definitions contradict, or a term
# nothing printed gives a meaning to, makes the list unread. A value with
# no normal form (an array over an index sort whose elements aren't
# known) is left out: that term is not determined. The model answers
# `None` everywhere else, so a term needing anything else evaluates to
# `NotGiven`.

module answer

import std.list
import std.bytes
import smtlib
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node, Shape)
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, SortDecl, Sig, Context, Defined)
import term (Head, Fun, Prim, Sel, Term, App, Op, Div, Mod, SeqNth)
import model (Value, Truth, Integer, Sequence, Constructed, Element, Model, Domain, UpTo, Unsized)
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

# An answer's text without the line Z3 prints for the query `src`'s
# `(get-unsat-core)` after `sat`: exactly `(error "line L column C: unsat
# core is not available")`, where `L` and `C` are where that command's
# closing parenthesis is (the line from 1, the column from 0, as Z3 counts
# them), alone on the line right after `sat`. Nothing else is removed: any
# other error, this one with another place, or this one anywhere else,
# stays and fails to read.
export fn without_core_error text src -> r : text~Bytes, src~Bytes, r~Bytes
    match core_error src
        Some line -> without_line text line
        None      -> text

fn without_line text expected -> r : text~Bytes, expected~Bytes, r~Bytes
    let i = after_comments text 0
    let j = line_end text i
    if bytes.slice text i j == b"sat" and j < len text
        let k = line_end text (j + 1)
        if bytes.slice text (j + 1) k == expected
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

# The error line Z3 prints for the first `(get-unsat-core)` of the query
# `src`, if it has one.
export fn core_error src -> r : src~Bytes, r~Option Bytes
    match smtlib.read src
        Ok es -> core_in src es
        Err _ -> None

fn core_in src es -> r : src~Bytes, es~List (SExpr src), r~Option Bytes
    match es
        []        -> None
        e :: rest ->
            match e
                Node [Leaf (Symbol g False) _] at if g == b"get-unsat-core" ->
                    match smtlib.end_of src at
                        Ok j  ->
                            let (l, c) = smtlib.position src (j - 1)
                            Some (b"(error \"line " ++ smtlib.numeral l ++ b" column " ++ smtlib.numeral (c - 1) ++ b": unsat core is not available\")")
                        Err _ -> None
                _ -> core_in src rest

# ── Values ───────────────────────────────────────────────────────────────────

# How many levels evaluation may go down running the query's definitions
# marked terminating (`smt.model`).
export let FUEL = 2000

# The `(get-value …)` terms of a query, as written: what `get-value` in
# `es`, the query's S-expressions, asks for.
export fn asked es -> r : es~List (SExpr src), r~List Shape
    match es
        []        -> []
        e :: rest ->
            match e
                Node [Leaf (Symbol g False) _, Node ts _] _ if g == b"get-value" -> smtlib.shapes ts
                _ -> asked rest

# The universes a model printed beside the values gives (none, for a
# `(get-value …)` answer alone): what the values are read with.
fn names_with c us -> n : c~Context, us~List (Sort, Nat), n~Names
    Names (term.signature c) [] us

fn defs_with c us -> d : c~Context, us~List (Sort, Nat), d~Defs
    Defs (term.signature c) (\u args -> domain_in us u args) []

# The elements of `Unin u args`: its universe's, if one was printed; else
# how many there are is not known.
export fn domain_in us u args -> d : us~List (Sort, Nat), u~Nat, args~List Sort, d~Domain
    match printed.universe us (Unin u args)
        Some n -> if n > 0 then UpTo (n - 1) else Unsized
        None   -> Unsized

# The value `e` writes, as a value of sort `s` in `c` with the universes
# `us`; `None` if it is an array with no normal form (a `store` or a
# `lambda` over an index sort whose elements aren't known): that value is
# not determined.
export fn value_of c us s e -> r : c~Context, us~List (Sort, Nat), s~Sort, e~SExpr src, r~Result (Option Value) Bytes
    let t = try printed.checked (names_with c us) [] s e
    match printed.eval (defs_with c us) 0 [] t
        Ok v  -> Ok (Some v)
        Err w -> if w == printed.NO_NORMAL_FORM or w == printed.INDEX_USED then Ok None else Err w

# The values printed for `terms` (in order, written `written` in the query)
# in an answer whose S-expressions are `es`: `sat`, then the one
# `(get-value …)` list, and nothing else.
export fn printed c terms written es -> r : c~Context, terms~List Term, written~List Shape, es~List (SExpr src),
                                            r~Result (List (Term, Value)) Bytes
    match es
        [Leaf (Symbol v False) _, vals] if v == b"sat" -> values_list c terms written vals [] True
        _ -> Err b"not `sat` and one `(get-value …)` list"

# The `(get-value …)` list `e` for `terms`, with the universes `us`: each
# printed term the one asked there, written the same way, with a value of
# its sort. The pairs must make one model (`model_of`), and each pair's
# term must have its printed value there, the query's definitions run as
# their bodies; if `placed`, each must also have a value there at all (a
# term nothing printed gives a meaning to makes the list unread). A value
# with no normal form is left out: it is not determined.
export fn values_list c terms written e us placed -> r : c~Context, terms~List Term, written~List Shape, e~SExpr src,
                                                         us~List (Sort, Nat), placed~Bool,
                                                         r~Result (List (Term, Value)) Bytes
    match e
        Node pairs _ ->
            let ps = try pair_values c us terms written pairs
            let m = model_of c us ps FUEL
            match unplaced c m ps placed
                Some w -> Err w
                None   -> Ok ps
        _            -> Err b"a `(get-value …)` answer that isn't a list"

fn pair_values c us terms written pairs -> r : c~Context, us~List (Sort, Nat), terms~List Term, written~List Shape,
                                               pairs~List (SExpr src), r~Result (List (Term, Value)) Bytes
    let sig = term.signature c
    match (terms, written, pairs)
        ([], [], [])                            -> Ok []
        (t :: tr, w :: wr, Node [p, e] _ :: pr) ->
            if smtlib.same sig w (smtlib.shape p)
                match term.sort_of sig [] t
                    Ok s  ->
                        let v = try value_of c us s e
                        let more = try pair_values c us tr wr pr
                        match v
                            Some x -> Ok ((t, x) :: more)
                            None   -> Ok more
                    Err _ -> Err b"a `get-value` term without a sort"
            else
                Err b"a printed value for a term other than the one asked for there"
        _                                       -> Err b"the values printed don't match the terms asked for"

# Why the pairs `ps` don't make the model `m`, if they don't: a pair whose
# term has another value there, or (if `placed`) none.
fn unplaced c m ps placed -> r : c~Context, m~Model, ps~List (Term, Value), placed~Bool, r~Option Bytes
    match ps
        []             -> None
        (t, v) :: rest ->
            match model.eval_unfolding c m t
                Ok w  -> if w == v then unplaced c m rest placed else Some b"values printed that contradict each other, or the query's definitions"
                Err _ ->
                    if placed
                        Some b"a value printed for a term the other values give no meaning to"
                    else
                        unplaced c m rest placed

# Whether each printed value is what its term evaluates to in `m`, a
# model printed beside the values, wherever `m` determines it.
export fn given_by c ps m -> r : c~Context, ps~List (Term, Value), m~Model, r~Bool
    match ps
        []             -> True
        (t, v) :: rest ->
            match model.eval_unfolding c m t
                Ok w  -> w == v and given_by c rest m
                Err _ -> given_by c rest m

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

# The values of `ts` in `m`, if each has one.
fn known c m ts -> r : c~Context, m~Model, ts~List Term, r~Option (List Value)
    match ts
        []        -> Some []
        t :: rest ->
            match (model.eval_unfolding c m t, known c m rest)
                (Ok v, Some vs) -> Some (v :: vs)
                _               -> None

# What `t` printed as `v` says, where `m` gives the values of its
# arguments: a declared function's value at them, `div` or `mod` by zero,
# `seq.nth` out of range, or a selector applied to another constructor's
# value. Anything else says nothing by itself (a definition's value is its
# body's).
fn says c m t v -> r : c~Context, m~Model, t~Term, v~Value, r~Says
    let sig = term.signature c
    match t
        App (Fun f) args         ->
            if f < len sig.funs and sig.funs[f].kind != Defined
                match known c m args
                    Some vs -> FunAt f vs v
                    None    -> Nothing
            else
                Nothing
        App (Prim Div) [a, b]    ->
            match (known c m [a, b], v)
                (Some [Integer n, Integer 0], Integer w) -> DivAt n w
                _                                        -> Nothing
        App (Prim Mod) [a, b]    ->
            match (known c m [a, b], v)
                (Some [Integer n, Integer 0], Integer w) -> ModAt n w
                _                                        -> Nothing
        App (Prim SeqNth) [a, b] ->
            match (known c m [a, b], term.sort_of sig [] t)
                (Some [Sequence xs, Integer i], Ok e) ->
                    if 0 <= i and i < list.length xs then Nothing else NthAt e xs i v
                _                                     -> Nothing
        App (Sel d k j) [a]      ->
            match (known c m [a], term.sort_of sig [] a)
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

# The model that says exactly `ss`, and nothing else, with the universes
# `us`.
fn said c us ss fuel -> m : c~Context, us~List (Sort, Nat), ss~List Says, fuel~Nat, m~Model
    let funs = \f vs -> fun_at ss f vs
    let nth = \e xs i -> nth_at ss e xs i
    let sel = \d k j args x -> sel_at ss d k j args x
    let dom = \u args -> domain_in us u args
    model.normal_arrays (term.signature c) (model.without_arrays funs (\n -> div_at ss n) (\n -> mod_at ss n) nth sel dom fuel)

# What the pairs say, placed in rounds: a pair's arguments are evaluated in
# the model the pairs placed so far make (`x` before `(f x)`). A round
# places at least one more pair or is the last, so there are at most as
# many rounds as pairs.
fn settle c us ps ss left fuel -> r : c~Context, us~List (Sort, Nat), ps~List (Term, Value), ss~List Says, left~Nat,
                                      fuel~Nat, r~List Says
    decreasing left
    let next = list.map (\(t, v) -> says c (said c us ss fuel) t v) ps
    if left == 0 or next == ss then next else settle c us ps next (left - 1) fuel

# The model that says exactly what was printed (`pairs`), and nothing else:
# an uninterpreted sort's size only if a universe for it is in `us`, and
# evaluation running definitions marked terminating `fuel` levels deep.
export fn model_of c us pairs fuel -> m : c~Context, us~List (Sort, Nat), pairs~List (Term, Value), fuel~Nat, m~Model
    let none = list.map (\_ -> Nothing) pairs
    said c us (settle c us pairs none (list.length pairs + 1) fuel) fuel
