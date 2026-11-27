# z3model.ck — the model Z3 prints for `(get-model)`, as a `Model`.
#
# Z3 5.3.3 prints, for a `sat` query, one `define-fun` for each declared
# constant and function it gave an interpretation to: a value for a
# constant, and for a function a body over its parameters `x!0`, `x!1`, …,
# usually an `ite` chain ending in a default. It also prints:
#
# - `div0` and `mod0` (two `Int` parameters): `div` and `mod` by zero;
# - `seq.nth_u` (a sequence and an `Int`): `seq.nth` out of range;
# - `k!N`: functions an array is made from, as `(_ as-array k!N)`;
# - for each uninterpreted sort, its universe: `(declare-fun S!val!N () S)`
#   for each element, and a cardinality constraint.
#
# It does not print the definitions of `define-fun-rec` (they are the
# query's own, and `smt.model` runs them as their bodies), nor selectors
# applied to another constructor's value: their values exist in Z3's model
# but `get-model` leaves them out.
#
# Named assertions are printed too, as `Bool` constants; they are the
# query's names, and `smt.model` doesn't use them.
#
# A body is evaluated here, at the arguments `smt.model` asks for, by
# `interp`, which knows the forms Z3 prints and nothing else. It reads
# exactly the model printed, or doesn't read it (as `answer` does): a name
# is the innermost binding of it (`answer.Bind`: a parameter, a `let`, a
# `lambda`'s variable) before it is a definition of the model; a model
# whose names could be read two ways is not read at all (`full`); a form it
# doesn't know, or an `as` of another sort, is not evaluated.

module z3model

import std.list
import std.bytes
import answer
import answer (Bind, Known, Later, Index)
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node)
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, Sig, Context)
import term (Command, DeclareSort, DeclareDatatypes, DeclareFun, DefineFuns, Assume, Assert)
import model (Value, Truth, Integer, Sequence, Constructed, Element, ArrayElem)
import model (Model, Domain, UpTo, Countable)

# A `define-fun` Z3 printed.
record Printed src : src~Bytes
    name~Name
    params~List (Name, Sort)
    result~Sort
    body~SExpr src

# What a `(get-model)` printed: its definitions, and how many elements
# each uninterpreted sort has.
export record Full src : src~Bytes
    defs~List (Printed src)
    universes~List (Sort, List Nat)

# ── Reading the model ────────────────────────────────────────────────────────

fn params_from sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List (Name, Sort)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, s] _ :: rest ->
            let sort = try answer.sort_from sig s
            let more = try params_from sig rest
            Ok ((n, sort) :: more)
        _                                       -> Err b"a parameter that isn't `(NAME SORT)`"

# `us` with element `k` of sort `s` added.
fn bump us s k -> r : us~List (Sort, List Nat), s~Sort, k~Nat, r~List (Sort, List Nat)
    match us
        []              -> [(s, [k])]
        (t, ks) :: rest -> if t == s then (t, k :: ks) :: rest else (t, ks) :: bump rest s k

# The model in the items of a `(get-model)` list, for context `c`. It is
# not read when a name in it could be read two ways: the query introduces
# a name with `!` (Z3's own names have one: `k!1`, `S!val!0`, `x!0`), it
# defines one name twice, or it defines a name that is neither the
# query's nor one Z3 is measured to print (`div0`, `mod0`, `seq.nth_u`,
# `k!N`).
export fn full c items -> r : c~Context, items~List (SExpr src), r~Result (Full src) Bytes
    let sig = term.signature c
    let names = query_names c
    if bang c
        Err BANG
    else
        let f = try read_items sig items
        match first_unknown names f.defs
            Some n -> Err (b"a definition of a name that is neither the query's nor Z3's: " ++ n)
            None   ->
                if twice f.defs
                    Err b"two definitions of one name"
                else if not (list.all (\(_, ks) -> numbered_from ks) f.universes)
                    Err b"a universe whose elements aren't numbered 0 to its size"
                else
                    Ok f

# Whether the query introduces a name with `!`, as Z3's own names in a
# model have: such a query gets no model read.
export fn bang c -> r : c~Context, r~Bool
    not (list.all (\n -> not (has_bang n 0)) (query_names c))

export let BANG = b"the query introduces a name with `!`, as Z3's own names in a model are"

fn read_items sig items -> r : sig~Sig, items~List (SExpr src), r~Result (Full src) Bytes
    match items
        []        -> Ok (Full [] [])
        e :: rest ->
            let f = try read_items sig rest
            match e
                Node [Leaf (Symbol k False) _, Leaf (Symbol n _) _, Node ps _, s, body] _ if k == b"define-fun" ->
                    let params = try params_from sig ps
                    let result = try answer.sort_from sig s
                    Ok (Full (Printed n params result body :: f.defs) f.universes)
                Node [Leaf (Symbol k False) _, Leaf (Symbol n _) _, Node [] _, s] _ if k == b"declare-fun" ->
                    let sort = try answer.sort_from sig s
                    match element_of sig sort n
                        Some e -> Ok (Full f.defs (bump f.universes sort e))
                        None   -> Err (b"a `declare-fun` that isn't an element of an uninterpreted sort: " ++ n)
                Node (Leaf (Symbol k False) _ :: _) _ if k == b"forall" -> Ok f
                _ -> Err b"an item of the model that isn't `define-fun`, `declare-fun` or a cardinality constraint"

# Whether `ks` are `0`, …, `n - 1` for `n` its length, each once.
fn numbered_from ks -> r : ks~List Nat, r~Bool
    list.unique ks and list.all (\k -> k < list.length ks) ks

fn has_bang n i -> r : n~Name, i~Nat, i <= len n, r~Bool
    decreasing len n - i
    if i >= len n then False else n[i] == '!' or has_bang n (i + 1)

# Every name the query introduces: sorts, datatypes, constructors,
# selectors, functions, assertion names.
fn query_names c -> r : c~Context, r~List Name
    names_in (term.commands c)

fn names_in cs -> r : cs~List Command, r~List Name
    match cs
        []          -> []
        cmd :: rest -> command_names cmd ++ names_in rest

fn command_names cmd -> r : cmd~Command, r~List Name
    match cmd
        DeclareSort d       -> [d.name]
        DeclareDatatypes ds -> all_names (list.map datatype_names ds)
        DeclareFun f        -> [f.name]
        DefineFuns _ ds     -> list.map (\d -> d.name) ds
        Assume _ n          -> option_name n
        Assert _ n          -> option_name n

fn option_name n -> r : n~Option Name, r~List Name
    match n
        Some x -> [x]
        None   -> []

fn datatype_names d -> r : d~Datatype, r~List Name
    d.name :: all_names (list.map ctor_names d.ctors)

fn ctor_names c -> r : c~Ctor, r~List Name
    c.name :: list.map (\f -> f.name) c.fields

fn all_names xss -> r : xss~List (List Name), r~List Name
    match xss
        []         -> []
        xs :: rest -> xs ++ all_names rest

# Whether `n` is a name Z3 is measured to define in a model of its own.
fn z3_name n -> r : n~Name, r~Bool
    n == b"div0" or n == b"mod0" or n == b"seq.nth_u"
        or (len n > 2 and bytes.matches_at n 0 b"k!" and answer.digits_value (bytes.slice n 2 (len n)) != None)

fn first_unknown names ds -> r : names~List Name, ds~List (Printed src), r~Option Name
    match ds
        []        -> None
        d :: rest -> if z3_name d.name or list.contains names d.name then first_unknown names rest else Some d.name

fn twice ds -> r : ds~List (Printed src), r~Bool
    match ds
        []        -> False
        d :: rest -> has_name rest d.name or twice rest

fn find_def ds n arity -> r : ds~List (Printed src), n~Name, arity~Nat, r~Option (Printed src)
    match ds
        []        -> None
        d :: rest -> if d.name == n and list.length d.params == arity then Some d else find_def rest n arity

# ── Evaluating what Z3 printed ───────────────────────────────────────────────

let TOO_DEEP = b"Z3's model nests too deep"

# How deep evaluation of the model's bodies may go.
let DEPTH = 100000

type Scope src = sc~List (Bind src)

fn element_of sig s n -> r : sig~Sig, s~Sort, n~Name, r~Option Nat
    match s
        Unin u _ -> if u < len sig.sorts then answer.element_number sig.sorts[u].name n else None
        _        -> None

# The sort `e` has, where it can be told without an expected sort.
fn sort_of_expr sig full scope e depth -> r : sig~Sig, full~Full src, scope~Scope src, e~SExpr src, depth~Nat,
                                              r~Option Sort
    decreasing depth
    if depth == 0
        None
    else
        match e
            Leaf (Numeral _) _                       -> Some Int
            Leaf (Symbol n _) _                      ->
                match answer.bound scope n
                    Some (Known _ _ s)  -> Some s
                    Some (Index _ s)    -> Some s
                    Some (Later _ x sc) -> sort_of_expr sig full sc x (depth - 1)
                    None                ->
                        if n == b"true" or n == b"false"
                            Some Bool
                        else
                            match find_def full.defs n 0
                                Some d -> Some d.result
                                None   -> ctor_sort sig n 0
            Node [Leaf (Symbol a False) _, _, s] _ if a == b"as" ->
                match answer.sort_from sig s
                    Ok x  -> Some x
                    Err _ -> None
            Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
                match answer.let_binds binds scope
                    Ok more -> sort_of_expr sig full (more ++ scope) body (depth - 1)
                    Err _   -> None
            Node (Leaf (Symbol n False) _ :: args) _ ->
                if n == b"+" or n == b"-" or n == b"*" or n == b"div" or n == b"mod" or n == b"seq.len"
                    Some Int
                else if n == b"<" or n == b"<=" or n == b">" or n == b">=" or n == b"=" or n == b"and" or n == b"or"
                    or n == b"not" or n == b"=>"
                    Some Bool
                else if n == b"ite"
                    match args
                        [_, a, b] ->
                            match sort_of_expr sig full scope a (depth - 1)
                                Some s -> Some s
                                None   -> sort_of_expr sig full scope b (depth - 1)
                        _         -> None
                else if n == b"seq.unit"
                    match args
                        [a] ->
                            match sort_of_expr sig full scope a (depth - 1)
                                Some s -> Some (Seq s)
                                None   -> None
                        _   -> None
                else if n == b"seq.++" or n == b"store"
                    match args
                        a :: _ -> sort_of_expr sig full scope a (depth - 1)
                        []     -> None
                else if n == b"select"
                    match args
                        [a, _] ->
                            match sort_of_expr sig full scope a (depth - 1)
                                Some (Arr _ v) -> Some v
                                _              -> None
                        _      -> None
                else
                    match find_def full.defs n (list.length args)
                        Some d -> Some d.result
                        None   -> ctor_sort sig n 0
            Node (Node [Leaf (Symbol a False) _, _, s] _ :: _) _ if a == b"as" ->
                match answer.sort_from sig s
                    Ok x  -> Some x
                    Err _ -> None
            _                                        -> None

# The sort of constructor `n`'s values, if its datatype has no parameters.
fn ctor_sort sig n d -> r : sig~Sig, n~Name, d~Nat, d <= len sig.datatypes, r~Option Sort
    decreasing len sig.datatypes - d
    if d >= len sig.datatypes
        None
    else if sig.datatypes[d].params == [] and answer.ctor_named sig.datatypes[d].ctors n 0 != None
        Some (Data d [])
    else
        ctor_sort sig n (d + 1)

fn as_bool r -> b : r~Result Value Bytes, b~Result Bool Bytes
    match r
        Ok (Truth x) -> Ok x
        Ok _         -> Err b"not a Bool"
        Err e        -> Err e

fn as_int r -> n : r~Result Value Bytes, n~Result Int Bytes
    match r
        Ok (Integer x) -> Ok x
        Ok _           -> Err b"not an Int"
        Err e          -> Err e

# The value of `e`, of sort `s`, with the names `scope` binds.
fn interp sig full scope s e depth -> r : sig~Sig, full~Full src, scope~Scope src, s~Sort, e~SExpr src, depth~Nat,
                                          r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let d = depth - 1
        match e
            Leaf (Symbol n _) _                      ->
                match answer.bound scope n
                    Some (Known _ v t)  -> if t == s then Ok v else Err b"a name of another sort"
                    Some (Later _ x sc) -> interp sig full sc s x d
                    Some (Index _ _)    -> Err answer.INDEX_USED
                    None                ->
                        match find_def full.defs n 0
                            Some p -> if p.result == s then interp sig full [] p.result p.body d else Err b"a constant of another sort"
                            None   ->
                                match element_of sig s n
                                    Some k -> Ok (Element k)
                                    None   -> answer.value_from sig s e [] d
            Leaf _ _                                 -> answer.value_from sig s e [] d
            Node [Leaf (Symbol l False) _, _, _] _ if l == b"lambda" -> array_from sig full scope s e d
            Node [Leaf (Symbol u False) _, Leaf (Symbol a False) _, _] _ if u == b"_" and a == b"as-array" ->
                array_from sig full scope s e d
            Node [Leaf (Symbol m False) _, Leaf (Numeral n) _] _ if m == b"-" ->
                match s
                    Int -> Ok (Integer (0 - n))
                    _   -> Err b"a negative numeral where the sort isn't Int"
            Node [Leaf (Symbol a False) _, _, _] _ if a == b"as" -> answer.value_from sig s e [] d
            Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
                let more = try answer.let_binds binds scope
                interp sig full (more ++ scope) s body d
            Node (Leaf (Symbol n False) _ :: args) _ -> call sig full scope s n args d
            Node (Node [Leaf (Symbol a False) _, Leaf (Symbol c _) _, t] _ :: args) _ if a == b"as" ->
                let _ = try answer.as_sort sig t s
                if c == b"const"
                    match (s, args)
                        (Arr _ v, [x]) ->
                            let w = try interp sig full scope v x d
                            match model.const_array sig (\u args -> domain_of full u args) s w
                                Some a -> Ok a
                                None   -> Err answer.NO_NORMAL_FORM
                        _              -> Err b"a constant array where the sort isn't an array"
                else
                    construct sig full scope s c args d
            _                                        -> answer.value_from sig s e [] d

# An array Z3 printed as a function of its index, a `lambda` or
# `(_ as-array f)`, as a normal form: when the function is a chain of
# `(ite (= x c) v …)` ending in a value that doesn't use `x`. Any other
# function (a range, `(<= 2 x)`) has no normal form, and isn't read. The
# index `x` shadows any name of the model; `c`, `v` and the value it ends
# in may not use it.
fn array_from sig full scope s e depth -> r : sig~Sig, full~Full src, scope~Scope src, s~Sort, e~SExpr src, depth~Nat,
                                              r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match (s, e)
            (Arr i w, Node [_, Node [Node [Leaf (Symbol x _) _, t] _] _, body] _) ->
                let _ = try answer.as_sort sig t i
                chain sig full (Index x i :: scope) s i w x body (depth - 1)
            (Arr i w, Node [_, _, Leaf (Symbol f _) _] _)                         ->
                match find_def full.defs f 1
                    Some p ->
                        match p.params
                            [(x, t)] -> if t == i then chain sig full [Index x i] s i w x p.body (depth - 1) else Err b"an array whose function's parameter is of another sort"
                            _        -> Err answer.NO_NORMAL_FORM
                    None   -> Err b"an array whose function Z3 didn't print"
            _                                                                     -> Err answer.NO_NORMAL_FORM

# The array whose index `x` is mapped by `body`: stores for each
# `(ite (= x c) v rest)`, outermost hiding the rest, over the constant
# `rest` ends in.
fn chain sig full scope s i w x body depth -> r : sig~Sig, full~Full src, scope~Scope src, s~Sort, i~Sort, w~Sort, x~Name,
                                                  body~SExpr src, depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let d = depth - 1
        let dom = \u args -> domain_of full u args
        match body
            Node [Leaf (Symbol ite False) _, Node [Leaf (Symbol eq False) _, l, r] _, v, rest] _ if ite == b"ite" and eq == b"=" ->
                let c = try (if is_var l x then interp sig full scope i r d else if is_var r x then interp sig full scope i l d else Err answer.NO_NORMAL_FORM)
                let at = try interp sig full scope w v d
                let under = try chain sig full scope s i w x rest d
                match model.store_array sig dom s under c at
                    Some a -> Ok a
                    None   -> Err answer.NO_NORMAL_FORM
            _ ->
                let base = try interp sig full scope w body d
                match model.const_array sig dom s base
                    Some a -> Ok a
                    None   -> Err answer.NO_NORMAL_FORM

fn is_var e x -> r : e~SExpr src, x~Name, r~Bool
    match e
        Leaf (Symbol n _) _ -> n == x
        _                   -> False

# `n` applied to `args`.
fn call sig full scope s n args depth -> r : sig~Sig, full~Full src, scope~Scope src, s~Sort, n~Name, args~List (SExpr src),
                                             depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let d = depth - 1
        let bool = \x -> as_bool (interp sig full scope Bool x d)
        let int = \x -> as_int (interp sig full scope Int x d)
        match (n, args)
            (_, [c, a, b]) if n == b"ite" ->
                let cv = try bool c
                if cv then interp sig full scope s a d else interp sig full scope s b d
            (_, [a]) if n == b"not" ->
                let x = try bool a
                Ok (Truth (not x))
            (_, _) if n == b"and" -> conj sig full scope args d
            (_, _) if n == b"or" -> disj sig full scope args d
            (_, [a, b]) if n == b"=>" ->
                let x = try bool a
                let y = try bool b
                Ok (Truth (not x or y))
            (_, [a, b]) if n == b"=" ->
                let sort =
                    match sort_of_expr sig full scope a d
                        Some x -> Some x
                        None   -> sort_of_expr sig full scope b d
                match sort
                    Some t ->
                        let x = try interp sig full scope t a d
                        let y = try interp sig full scope t b d
                        Ok (Truth (x == y))
                    None   -> Err b"`=` of terms whose sort this reader can't tell"
            (_, [a, b]) if n == b"+" -> arith (int a) (int b) (\x y -> Ok (Integer (x + y)))
            (_, [a, b]) if n == b"-" -> arith (int a) (int b) (\x y -> Ok (Integer (x - y)))
            (_, [a]) if n == b"-" ->
                let x = try int a
                Ok (Integer (0 - x))
            (_, [a, b]) if n == b"*" -> arith (int a) (int b) (\x y -> Ok (Integer (x * y)))
            (_, [a, b]) if n == b"<" -> arith (int a) (int b) (\x y -> Ok (Truth (x < y)))
            (_, [a, b]) if n == b"<=" -> arith (int a) (int b) (\x y -> Ok (Truth (x <= y)))
            (_, [a, b]) if n == b">" -> arith (int a) (int b) (\x y -> Ok (Truth (x > y)))
            (_, [a, b]) if n == b">=" -> arith (int a) (int b) (\x y -> Ok (Truth (x >= y)))
            (_, [a]) if n == b"seq.unit" ->
                match s
                    Seq el ->
                        let x = try interp sig full scope el a d
                        Ok (Sequence [x])
                    _      -> Err b"seq.unit where the sort isn't a sequence"
            (_, _) if n == b"seq.++" -> concat sig full scope s args d
            (_, [a, i, v]) if n == b"store" ->
                match s
                    Arr is vs ->
                        let x = try interp sig full scope s a d
                        let j = try interp sig full scope is i d
                        let w = try interp sig full scope vs v d
                        match model.store_array sig (\u args -> domain_of full u args) s x j w
                            Some a -> Ok a
                            None   -> Err answer.NO_NORMAL_FORM
                    _         -> Err b"store where the sort isn't an array"
            _ ->
                match answer.bound scope n
                    Some _ -> Err (b"a bound name applied to arguments: " ++ n)
                    None   ->
                        match find_def full.defs n (list.length args)
                            Some p ->
                                if p.result == s
                                    let vs = try interp_all sig full scope (list.map (\(_, t) -> t) p.params) args d
                                    interp sig full (bind p.params vs) p.result p.body d
                                else
                                    Err b"a function of another sort"
                            None   -> construct sig full scope s n args d

fn bind ps vs -> r : ps~List (Name, Sort), vs~List Value, r~Scope src
    match (ps, vs)
        ((n, s) :: pr, v :: vr) -> Known n v s :: bind pr vr
        _                       -> []

fn arith rx ry f -> r : rx~Result Int Bytes, ry~Result Int Bytes, f~(Int -> Int -> Result Value Bytes),
                        r~Result Value Bytes
    let x = try rx
    let y = try ry
    f x y

fn conj sig full scope args depth -> r : sig~Sig, full~Full src, scope~Scope src, args~List (SExpr src), depth~Nat,
                                         r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match args
            []        -> Ok (Truth True)
            a :: rest ->
                match interp sig full scope Bool a (depth - 1)
                    Ok (Truth False) -> Ok (Truth False)
                    Ok (Truth True)  -> conj sig full scope rest (depth - 1)
                    Ok _             -> Err b"not a Bool"
                    Err e            -> Err e

fn disj sig full scope args depth -> r : sig~Sig, full~Full src, scope~Scope src, args~List (SExpr src), depth~Nat,
                                         r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match args
            []        -> Ok (Truth False)
            a :: rest ->
                match interp sig full scope Bool a (depth - 1)
                    Ok (Truth True)  -> Ok (Truth True)
                    Ok (Truth False) -> disj sig full scope rest (depth - 1)
                    Ok _             -> Err b"not a Bool"
                    Err e            -> Err e

fn concat sig full scope s args depth -> r : sig~Sig, full~Full src, scope~Scope src, s~Sort, args~List (SExpr src),
                                             depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match args
            []        -> Ok (Sequence [])
            a :: rest ->
                let x = try interp sig full scope s a (depth - 1)
                let y = try concat sig full scope s rest (depth - 1)
                match (x, y)
                    (Sequence xs, Sequence ys) -> Ok (Sequence (xs ++ ys))
                    _                          -> Err b"seq.++ of something that isn't a sequence"

fn interp_all sig full scope ss es depth -> r : sig~Sig, full~Full src, scope~Scope src, ss~List Sort, es~List (SExpr src),
                                                depth~Nat, r~Result (List Value) Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match (ss, es)
            ([], [])           -> Ok []
            (s :: sr, e :: er) ->
                let v = try interp sig full scope s e (depth - 1)
                let vs = try interp_all sig full scope sr er (depth - 1)
                Ok (v :: vs)
            _                  -> Err b"a call with the wrong number of arguments"

# Constructor `n` of `s` applied to `args`.
fn construct sig full scope s n args depth -> r : sig~Sig, full~Full src, scope~Scope src, s~Sort, n~Name,
                                                  args~List (SExpr src), depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match s
            Data d sargs ->
                if d < len sig.datatypes
                    match answer.ctor_named sig.datatypes[d].ctors n 0
                        Some (k, c) ->
                            let ss = list.map (term.instantiate sargs) (term.field_sorts c.fields)
                            let fs = try interp_all sig full scope ss args (depth - 1)
                            Ok (Constructed k fs)
                        None        -> Err (b"a form this reader doesn't know: `" ++ n ++ b"`")
                else
                    Err b"an undeclared datatype"
            _            -> Err (b"a form this reader doesn't know: `" ++ n ++ b"`")

# ── The model ────────────────────────────────────────────────────────────────

# `d` at the arguments `vs`.
fn apply_def sig full d vs -> r : sig~Sig, full~Full src, d~Printed src, vs~List Value, r~Option Value
    if list.length vs != list.length d.params
        None
    else
        match interp sig full (bind d.params vs) d.result d.body DEPTH
            Ok v  -> Some v
            Err _ -> None

# The `seq.nth_u` for sequences of `e`.
fn nth_def ds e -> r : ds~List (Printed src), e~Sort, r~Option (Printed src)
    match ds
        []        -> None
        d :: rest ->
            match d.params
                [(_, Seq x), (_, Int)] if d.name == b"seq.nth_u" and x == e and d.result == e -> Some d
                _ -> nth_def rest e

# The elements Z3 printed for `Unin u args`; a sort it printed none for
# appears in no term, and is taken as countable.
fn domain_of full u args -> r : full~Full src, u~Nat, args~List Sort, r~Domain
    match universe full.universes (Unin u args)
        Some n -> if n > 0 then UpTo (n - 1) else Countable
        None   -> Countable

fn universe us s -> r : us~List (Sort, List Nat), s~Sort, r~Option Nat
    match us
        []              -> None
        (t, ks) :: rest -> if t == s then Some (list.length ks) else universe rest s

# The `f`-th function at `vs`, if Z3 printed it with the sorts it was
# declared with.
fn fun_at sig full f vs -> r : sig~Sig, full~Full src, f~Nat, vs~List Value, r~Option Value
    if f < len sig.funs
        match find_def full.defs sig.funs[f].name (list.length vs)
            Some d ->
                if list.map (\(_, t) -> t) d.params == sig.funs[f].params and d.result == sig.funs[f].result
                    apply_def sig full d vs
                else
                    None
            None   -> None
    else
        None

fn int_of r -> n : r~Option Value, n~Option Int
    match r
        Some (Integer x) -> Some x
        _                -> None

fn by_zero sig full name n -> r : sig~Sig, full~Full src, name~Name, n~Int, r~Option Int
    match find_def full.defs name 2
        Some d ->
            match (d.params, d.result)
                ([(_, Int), (_, Int)], Int) -> int_of (apply_def sig full d [Integer n, Integer 0])
                _                           -> None
        None   -> None

# The model `full` describes, for `c`. Selectors of another constructor's
# value are not printed, so the model doesn't say them.
export fn model_of c full fuel -> m : c~Context, full~Full src, fuel~Nat, m~Model
    let sig = term.signature c
    let funs = \f vs -> fun_at sig full f vs
    let div_zero = \n -> by_zero sig full b"div0" n
    let mod_zero = \n -> by_zero sig full b"mod0" n
    let nth = \e xs i ->
        match nth_def full.defs e
            Some d -> apply_def sig full d [Sequence xs, Integer i]
            None   -> None
    let none5 = \_ _ _ _ _ -> None
    let domain = \u args -> domain_of full u args
    model.normal_arrays sig (model.without_arrays funs div_zero mod_zero nth none5 domain fuel)

# Whether Z3 printed an interpretation of the `f`-th function.
export fn printed_fun sig full f -> r : sig~Sig, full~Full src, f~Nat, r~Bool
    f < len sig.funs and has_name full.defs sig.funs[f].name

fn has_name ds n -> r : ds~List (Printed src), n~Name, r~Bool
    match ds
        []        -> False
        d :: rest -> d.name == n or has_name rest n

# Whether Z3 printed a definition named `n`.
export fn printed_name full n -> r : full~Full src, n~Name, r~Bool
    has_name full.defs n
