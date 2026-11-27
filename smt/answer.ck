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
import smtlib
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node, Shape)
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

# An answer's text without the line Z3 prints for `(get-unsat-core)` after
# `sat`, `(error "line L column C: unsat core is not available")`, which a
# query that asks for a core gets with every `sat`. Only that line: any
# other error still fails to read.
export fn without_core_error text -> r : text~Bytes, r~Bytes
    keep_lines text 0

fn keep_lines text i -> r : text~Bytes, i~Nat, i <= len text, r~Bytes
    decreasing len text - i
    if i >= len text
        b""
    else
        let j = line_end text i
        let line = bytes.slice text i j
        let rest = if j < len text then keep_lines text (j + 1) else b""
        let ended = if j < len text then line ++ b"\n" else line
        if no_core line then rest else ended ++ rest

fn no_core line -> r : line~Bytes, r~Bool
    let head = b"(error \"line "
    let tail = b": unsat core is not available\")"
    len line >= len head + len tail and bytes.matches_at line 0 head and bytes.matches_at line (len line - len tail) tail

# ── Reading what Z3 printed ──────────────────────────────────────────────────
# This reader and `z3model`'s read exactly what Z3 printed, or don't read
# it: a form they don't know, a name they can't resolve, a sort other than
# the one expected, or anything printed besides what the query asked for
# leaves the answer unread. They never guess.

# What a name stands for where a printed term is read: a value (a
# parameter's, with its sort), a `let`'s term with the names around that
# `let` (SMT-LIB's `let` is parallel: its terms see only what is around
# it), or a `lambda`'s variable, which a value can't use.
export enum Bind src : src~Bytes
    Known n v s     : n~Name, v~Value, s~Sort
    Later n e scope : n~Name, e~SExpr src, scope~List (Bind src)
    Index n s       : n~Name, s~Sort

fn bind_name b -> r : b~Bind src, r~Name
    match b
        Known n _ _ -> n
        Later n _ _ -> n
        Index n _   -> n

# The innermost binding of `n` in `scope`.
export fn bound scope n -> r : scope~List (Bind src), n~Name, r~Option (Bind src)
    match scope
        []        -> None
        b :: rest -> if bind_name b == n then Some b else bound rest n

# A `let`'s bindings, each with the scope around the `let`. Two bindings of
# one name in one `let` are an error in SMT-LIB, and not read here.
export fn let_binds es scope -> r : es~List (SExpr src), scope~List (Bind src), r~Result (List (Bind src)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, e] _ :: rest ->
            let more = try let_binds rest scope
            if bound more n != None then Err (b"a `let` that binds one name twice: " ++ n) else Ok (Later n e scope :: more)
        _                                       -> Err b"a `let` binding that isn't `(NAME VALUE)`"

export let INDEX_USED = b"a value that uses a `lambda`'s variable"

export fn ctor_named cs n k -> r : cs~List Ctor, n~Name, k~Nat, r~Option (Nat, Ctor)
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
export fn element_number sort_name n -> r : sort_name~Name, n~Name, r~Option Nat
    let prefix = sort_name ++ b"!val!"
    if len n > len prefix and bytes.matches_at n 0 prefix then digits_value (bytes.slice n (len prefix) (len n)) else None

# ── Sorts ────────────────────────────────────────────────────────────────────

fn find_sort_named sig n i -> r : sig~Sig, n~Name, i~Nat, i <= len sig.sorts, r~Option Nat
    decreasing len sig.sorts - i
    if i >= len sig.sorts then None else if sig.sorts[i].name == n then Some i else find_sort_named sig n (i + 1)

fn find_data_named sig n i -> r : sig~Sig, n~Name, i~Nat, i <= len sig.datatypes, r~Option Nat
    decreasing len sig.datatypes - i
    if i >= len sig.datatypes
        None
    else if sig.datatypes[i].name == n
        Some i
    else
        find_data_named sig n (i + 1)

# The sort `e` writes.
export fn sort_from sig e -> r : sig~Sig, e~SExpr src, r~Result Sort Bytes
    match e
        Leaf (Symbol n _) _                  -> named sig n []
        Node (Leaf (Symbol n _) _ :: args) _ ->
            let ss = try sorts_from sig args
            if n == b"Seq"
                match ss
                    [x] -> Ok (Seq x)
                    _   -> Err b"`Seq` with other than one sort"
            else if n == b"Array"
                match ss
                    [i, v] -> Ok (Arr i v)
                    _      -> Err b"`Array` with other than two sorts"
            else
                named sig n ss
        _                                    -> Err b"a sort this reader doesn't know"

fn sorts_from sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List Sort) Bytes
    match es
        []        -> Ok []
        e :: rest ->
            let s = try sort_from sig e
            let ss = try sorts_from sig rest
            Ok (s :: ss)

fn named sig n args -> r : sig~Sig, n~Name, args~List Sort, r~Result Sort Bytes
    if n == b"Int" and args == []
        Ok Int
    else if n == b"Bool" and args == []
        Ok Bool
    else
        match find_data_named sig n 0
            Some d -> Ok (Data d args)
            None   ->
                match find_sort_named sig n 0
                    Some u -> Ok (Unin u args)
                    None   -> Err (b"an unknown sort: " ++ n)

# Whether `(as … t)` names sort `s`; a different sort isn't read.
export fn as_sort sig t s -> r : sig~Sig, t~SExpr src, s~Sort, r~Result Unit Bytes
    let written = try sort_from sig t
    if written == s then Ok () else Err b"an `as` whose sort isn't the one expected"

# ── Values ───────────────────────────────────────────────────────────────────

# The value `e` writes, of sort `s` in `sig`, with the names of `scope`.
# `depth` bounds how deep it may nest (`let`s refer back).
export fn value_from sig s e scope depth -> r : sig~Sig, s~Sort, e~SExpr src, scope~List (Bind src), depth~Nat,
                                                r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match e
            Leaf (Symbol n _) _   ->
                match bound scope n
                    Some (Known _ v t)  -> if t == s then Ok v else Err b"a name of another sort"
                    Some (Later _ b sc) -> value_from sig s b sc less
                    Some (Index _ _)    -> Err INDEX_USED
                    None                -> symbol_value sig s n less
            Leaf (Numeral n) _    ->
                match s
                    Int -> Ok (Integer n)
                    _   -> Err b"a numeral where the sort isn't Int"
            Node [Leaf (Symbol m False) _, Leaf (Numeral n) _] _ if m == b"-" ->
                match s
                    Int -> Ok (Integer (0 - n))
                    _   -> Err b"a negative numeral where the sort isn't Int"
            Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
                let more = try let_binds binds scope
                value_from sig s body (more ++ scope) less
            Node [Leaf (Symbol a False) _, Leaf (Symbol n _) _, t] _ if a == b"as" ->
                let _ = try as_sort sig t s
                if n == b"seq.empty"
                    match s
                        Seq _ -> Ok (Sequence [])
                        _     -> Err b"seq.empty where the sort isn't a sequence"
                else
                    built sig s n [] scope less
            Node (head :: args) _ -> applied sig s head args scope less
            _                     -> Err b"a value outside what this reader knows"

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
fn built sig s n args scope depth -> r : sig~Sig, s~Sort, n~Name, args~List (SExpr src), scope~List (Bind src),
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
                            let fs = try fields_from sig (list.map (term.instantiate sargs) (term.field_sorts c.fields)) args scope less
                            Ok (Constructed k fs)
                        None        -> Err (b"not a constructor of the sort: " ++ n)
                else
                    Err b"an undeclared datatype"
            _            -> Err (b"a constructor where the sort isn't a datatype: " ++ n)

fn fields_from sig ss es scope depth -> r : sig~Sig, ss~List Sort, es~List (SExpr src), scope~List (Bind src),
                                            depth~Nat, r~Result (List Value) Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match (ss, es)
            ([], [])           -> Ok []
            (s :: sr, e :: er) ->
                let v = try value_from sig s e scope less
                let vs = try fields_from sig sr er scope less
                Ok (v :: vs)
            _                  -> Err b"a constructor with the wrong number of fields"

fn applied sig s head args scope depth -> r : sig~Sig, s~Sort, head~SExpr src, args~List (SExpr src),
                                              scope~List (Bind src), depth~Nat, r~Result Value Bytes
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
                            let v = try value_from sig el a scope less
                            Ok (Sequence [v])
                        _             -> Err b"seq.unit where the sort isn't a sequence"
                else if n == b"seq.++"
                    match s
                        Seq _ -> concat_from sig s args scope less
                        _     -> Err b"seq.++ where the sort isn't a sequence"
                else if n == b"store"
                    match (s, args)
                        (Arr i w, [a, j, x]) ->
                            let av = try value_from sig s a scope less
                            let jv = try value_from sig i j scope less
                            let xv = try value_from sig w x scope less
                            match model.store_array sig (\_ _ -> Countable) s av jv xv
                                Some v -> Ok v
                                None   -> Err NO_NORMAL_FORM
                        _                    -> Err b"store where the sort isn't an array"
                else
                    built sig s n args scope less
            Node [Leaf (Symbol a False) _, Leaf (Symbol n _) _, t] _ if a == b"as" ->
                let _ = try as_sort sig t s
                if n == b"const"
                    match (s, args)
                        (Arr _ w, [x]) ->
                            let v = try value_from sig w x scope less
                            match model.const_array sig (\_ _ -> Countable) s v
                                Some a -> Ok a
                                None   -> Err NO_NORMAL_FORM
                        _              -> Err b"a constant array where the sort isn't an array"
                else
                    built sig s n args scope less
            _                   -> Err b"a value outside what this reader knows"

fn concat_from sig s es scope depth -> r : sig~Sig, s~Sort, es~List (SExpr src), scope~List (Bind src), depth~Nat,
                                           r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let less = depth - 1
        match es
            []        -> Ok (Sequence [])
            e :: rest ->
                let v = try value_from sig s e scope less
                let w = try concat_from sig s rest scope less
                match (v, w)
                    (Sequence xs, Sequence ys) -> Ok (Sequence (xs ++ ys))
                    _                          -> Err b"seq.++ of something that isn't a sequence"

let TOO_DEEP = b"a value nested too deep"

export let NO_NORMAL_FORM = b"an array with no normal form: a store at an index sort `smt.model` can't show finite and listed, or unbounded"

# How deep a printed value may nest.
let DEPTH = 100000

# The `(get-value …)` terms of a query, as written: what `get-value` in
# `es`, the query's S-expressions, asks for.
export fn asked es -> r : es~List (SExpr src), r~List Shape
    match es
        []        -> []
        e :: rest ->
            match e
                Node [Leaf (Symbol g False) _, Node ts _] _ if g == b"get-value" -> smtlib.shapes ts
                _ -> asked rest

# The values printed for `terms` (in order, written `written` in the query)
# in an answer whose S-expressions are `es`: `sat`, then the one
# `(get-value …)` list, and nothing else. Each printed term must be the
# term asked for, written the same way.
export fn printed c terms written es -> r : c~Context, terms~List Term, written~List Shape, es~List (SExpr src),
                                            r~Result (List (Term, Value)) Bytes
    match es
        [Leaf (Symbol v False) _, Node pairs _] if v == b"sat" -> pair_values (term.signature c) terms written pairs
        _ -> Err b"not `sat` and one `(get-value …)` list"

export fn pair_values sig terms written pairs -> r : sig~Sig, terms~List Term, written~List Shape,
                                                     pairs~List (SExpr src), r~Result (List (Term, Value)) Bytes
    match (terms, written, pairs)
        ([], [], [])                            -> Ok []
        (t :: tr, w :: wr, Node [p, e] _ :: pr) ->
            if smtlib.same sig w (smtlib.shape p)
                match term.sort_of sig [] t
                    Ok s  ->
                        let v = try value_from sig s e [] DEPTH
                        let more = try pair_values sig tr wr pr
                        Ok ((t, v) :: more)
                    Err _ -> Err b"a `get-value` term without a sort"
            else
                Err b"a printed value for a term other than the one asked for there"
        _                                       -> Err b"the values printed don't match the terms asked for"

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
