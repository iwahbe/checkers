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
# `printed` reads the values; `model_of` makes them a `Model` that says
# only what was printed and answers `None` everywhere else, so that a term
# needing anything else evaluates to `NotGiven`.

module answer

import std.list
import std.bytes
import std.char
import std.string
import std.parse (Parsable)
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node)
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, SortDecl, Sig, Context)
import term (Head, Fun, Prim, Sel, Term, App, Op, Div, Mod, SeqNth)
import model (Value, Truth, Integer, Sequence, Constructed, Element, Model, Domain, Countable)

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

# ── Values ───────────────────────────────────────────────────────────────────

# A name Z3's `let` binds in a value (`a!1`) and what it stands for.
type Bound src = b~(Name, SExpr src)

fn find_bound lets n -> r : lets~List (Bound src), n~Name, r~Option (SExpr src)
    match lets
        []             -> None
        (m, e) :: rest -> if m == n then Some e else find_bound rest n

fn ctor_named cs n k -> r : cs~List Ctor, n~Name, k~Nat, r~Option (Nat, Ctor)
    match cs
        []        -> None
        c :: rest -> if c.name == n then Some (k, c) else ctor_named rest n (k + 1)

export fn digits_value b -> r : b~Bytes, r~Option Nat
    if len b > 0 and char.is_digit b[0]
        have string.parse_digits b
        match Parsable.parse b Int Int
            Ok (n, rest) -> if len rest == 0 then Some n else None
    else
        None

# `NAME!val!N`, Z3's name for element `N` of the sort `NAME`.
fn element_number sort_name n -> r : sort_name~Name, n~Name, r~Option Nat
    let prefix = sort_name ++ b"!val!"
    if len n > len prefix and bytes.matches_at n 0 prefix then digits_value (bytes.slice n (len prefix) (len n)) else None

# The value `e` writes, of sort `s` in `sig`; `lets` are the names bound
# around it. `depth` bounds how deep it may nest (`let`s refer back).
export fn value_from sig s e lets depth -> r : sig~Sig, s~Sort, e~SExpr src, lets~List (Bound src), depth~Nat,
                                               r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match e
            Leaf (Symbol n _) _   ->
                match find_bound lets n
                    Some b -> value_from sig s b lets less
                    None   -> symbol_value sig s n less
            Leaf (Numeral n) _    ->
                match s
                    Int -> Ok (Integer n)
                    _   -> Err b"a numeral where the sort isn't Int"
            Node [Leaf (Symbol m False) _, Leaf (Numeral n) _] _ if m == b"-" ->
                match s
                    Int -> Ok (Integer (0 - n))
                    _   -> Err b"a negative numeral where the sort isn't Int"
            Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
                let more = try let_binds binds
                value_from sig s body (list.reverse more ++ lets) less
            Node [Leaf (Symbol a False) _, Leaf (Symbol n _) _, _] _ if a == b"as" ->
                if n == b"seq.empty"
                    match s
                        Seq _ -> Ok (Sequence [])
                        _     -> Err b"seq.empty where the sort isn't a sequence"
                else
                    built sig s n [] lets less
            Node (head :: args) _ -> applied sig s head args lets less
            _                     -> Err b"a value outside what this reader knows"

fn let_binds es -> r : es~List (SExpr src), r~Result (List (Bound src)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, e] _ :: rest ->
            let more = try let_binds rest
            Ok ((n, e) :: more)
        _                                       -> Err b"a `let` binding that isn't `(NAME VALUE)`"

fn symbol_value sig s n depth -> r : sig~Sig, s~Sort, n~Name, depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match s
            Bool     -> if n == b"true" then Ok (Truth True) else if n == b"false" then Ok (Truth False) else Err b"not a Bool"
            Data _ _ -> built sig s n [] [] less
            Unin u _ ->
                if u < len sig.sorts
                    match element_number sig.sorts[u].name n
                        Some k -> Ok (Element k)
                        None   -> Err (b"not an element of " ++ sig.sorts[u].name ++ b": " ++ n)
                else
                    Err b"an undeclared sort"
            _        -> Err (b"a name where a value of this sort can't be one: " ++ n)

# Constructor `n` of `s` applied to `args`.
fn built sig s n args lets depth -> r : sig~Sig, s~Sort, n~Name, args~List (SExpr src), lets~List (Bound src),
                                        depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match s
            Data d sargs ->
                if d < len sig.datatypes
                    match ctor_named sig.datatypes[d].ctors n 0
                        Some (k, c) ->
                            let fs = try fields_from sig (list.map (term.instantiate sargs) (term.field_sorts c.fields)) args lets less
                            Ok (Constructed k fs)
                        None        -> Err (b"not a constructor of the sort: " ++ n)
                else
                    Err b"an undeclared datatype"
            _            -> Err (b"a constructor where the sort isn't a datatype: " ++ n)

fn fields_from sig ss es lets depth -> r : sig~Sig, ss~List Sort, es~List (SExpr src), lets~List (Bound src),
                                           depth~Nat, r~Result (List Value) Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match (ss, es)
            ([], [])           -> Ok []
            (s :: sr, e :: er) ->
                let v = try value_from sig s e lets less
                let vs = try fields_from sig sr er lets less
                Ok (v :: vs)
            _                  -> Err b"a constructor with the wrong number of fields"

fn applied sig s head args lets depth -> r : sig~Sig, s~Sort, head~SExpr src, args~List (SExpr src),
                                             lets~List (Bound src), depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match head
            Leaf (Symbol n _) _ ->
                if n == b"seq.unit"
                    match (s, args)
                        (Seq el, [a]) ->
                            let v = try value_from sig el a lets less
                            Ok (Sequence [v])
                        _             -> Err b"seq.unit where the sort isn't a sequence"
                else if n == b"seq.++"
                    match s
                        Seq _ -> concat_from sig s args lets less
                        _     -> Err b"seq.++ where the sort isn't a sequence"
                else if n == b"store"
                    match (s, args)
                        (Arr i w, [a, j, x]) ->
                            let av = try value_from sig s a lets less
                            let jv = try value_from sig i j lets less
                            let xv = try value_from sig w x lets less
                            match model.store_array sig (\_ _ -> Countable) s av jv xv
                                Some v -> Ok v
                                None   -> Err NO_NORMAL_FORM
                        _                    -> Err b"store where the sort isn't an array"
                else
                    built sig s n args lets less
            Node [Leaf (Symbol a False) _, Leaf (Symbol n _) _, _] _ if a == b"as" ->
                if n == b"const"
                    match (s, args)
                        (Arr i w, [x]) ->
                            let v = try value_from sig w x lets less
                            match model.const_array sig (\_ _ -> Countable) s v
                                Some a -> Ok a
                                None   -> Err NO_NORMAL_FORM
                        _              -> Err b"a constant array where the sort isn't an array"
                else
                    built sig s n args lets less
            _                   -> Err b"a value outside what this reader knows"

fn concat_from sig s es lets depth -> r : sig~Sig, s~Sort, es~List (SExpr src), lets~List (Bound src), depth~Nat,
                                          r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match es
            []        -> Ok (Sequence [])
            e :: rest ->
                let v = try value_from sig s e lets less
                let w = try concat_from sig s rest lets less
                match (v, w)
                    (Sequence xs, Sequence ys) -> Ok (Sequence (xs ++ ys))
                    _                          -> Err b"seq.++ of something that isn't a sequence"

let TOO_DEEP = b"a value nested too deep"

let NO_NORMAL_FORM = b"an array with no normal form (a store at an index sort `smt.model` can't show finite and listed, or unbounded)"

# How deep a printed value may nest.
let DEPTH = 100000

# The values printed for `terms` (in order), from the S-expressions of an
# answer: the last one is the `(get-value …)` list.
export fn printed c terms es -> r : c~Context, terms~List Term, es~List (SExpr src),
                                    r~Result (List (Term, Value)) Bytes
    match list.reverse es
        Node pairs _ :: _ -> pair_values (term.signature c) terms pairs
        _                 -> Err b"no `(get-value …)` output"

fn pair_values sig terms pairs -> r : sig~Sig, terms~List Term, pairs~List (SExpr src),
                                      r~Result (List (Term, Value)) Bytes
    match (terms, pairs)
        ([], [])                       -> Ok []
        (t :: tr, Node [_, e] _ :: pr) ->
            match term.sort_of sig [] t
                Ok s  ->
                    let v = try value_from sig s e [] DEPTH
                    let more = try pair_values sig tr pr
                    Ok ((t, v) :: more)
                Err _ -> Err b"a `get-value` term without a sort"
        _                              -> Err b"the values printed don't match the terms asked for"

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
# `normal_arrays` computes.
export fn empty_model sig fuel -> m : sig~Sig, fuel~Nat, m~Model
    let none5 = \_ _ _ _ _ -> None
    model.normal_arrays sig (model.without_arrays (\_ _ -> None) (\_ -> None) (\_ -> None) (\_ _ _ -> None) none5 (\_ _ -> Countable) fuel)

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
# uninterpreted sorts are taken as countable, which no ground term can
# tell apart from the finite domain Z3 chose, and it may go `fuel` levels
# deep.
export fn model_of c pairs fuel -> m : c~Context, pairs~List (Term, Value), fuel~Nat, m~Model
    let ss = list.map (\(t, v) -> says c fuel t v) pairs
    let funs = \f vs -> fun_at ss f vs
    let nth = \e xs i -> nth_at ss e xs i
    let sel = \d k j args x -> sel_at ss d k j args x
    model.normal_arrays (term.signature c) (model.without_arrays funs (\n -> div_at ss n) (\n -> mod_at ss n) nth sel (\_ _ -> Countable) fuel)
