# z3model.ck — the model Z3 prints for `(get-model)`, as a `Model`.
#
# Z3 5.3.3 prints, for a `sat` query, a `define-fun` for each declared
# constant and function it gave an interpretation to: a value for a
# constant, and for a function a body over its parameters. It also prints
# definitions of its own, measured on the corpus (every `sat` query, with
# `(get-model)`) as these and no others:
#
# - `div0` and `mod0` (two `Int` parameters, an `Int`): `div` and `mod` by
#   zero;
# - `seq.nth_u` (a sequence and an `Int`, an element), one for each sort of
#   sequence: `seq.nth` out of range;
# - `k!N`: a function an array is made of, as `(_ as-array k!N)`;
# - a `Bool` constant for each named assertion (the query's names), and
#   each constant the query defines (a `define-funs-rec` of no
#   parameters): each printed as a body, often the query's own term for it
#   (`(= (seq.len k) 2)`), sometimes a value.
#
# For an uninterpreted sort with a universe, it prints a
# `(declare-fun S!val!N () S)` for each element and a cardinality
# constraint, `(forall ((x S)) (= x S!val!0))` for one element and
# `(forall ((x S)) (or (= x S!val!0) …))` for more, its variable a name
# of Z3's own (`x`). An instance of a sort with parameters has a universe
# of its own, its elements spelled by the sort's name. A sort it prints no
# universe for has a size the model doesn't say. It doesn't print the
# query's definitions with parameters (`smt.model` runs them as their
# bodies), nor selectors applied to another constructor's value: those
# exist in Z3's model, but `get-model` leaves them out.
#
# A body uses the operations `printed` reads (`printed.checked`): every
# operation of the query's terms (`seq.extract` and `map +` among them),
# testers and selectors (a tester of a constructor without fields written
# alone, as Z3 prints `(is-none none)`), calls of the model's definitions,
# and calls of the query's own functions (read, and not evaluated).
#
# `full` reads the whole model first, and reads it only if all of it is
# as above: every name is one the model may define, once (`seq.nth_u` once
# for each sort), with distinct parameters and the sorts the query gives
# it; each universe's `declare-fun`s and its cardinality constraint name
# exactly the same elements, `S!val!0` to `S!val!(n-1)`, and its variable
# is spelled like no element and no name of the query or the model (else
# `(= x x)` could pass for a constraint); every body checks
# whole (`printed.checked`); no definition refers to itself, through
# others or not. A query that introduces a name with `!` (Z3's own names
# have one) gets no model read. Then `model_of` evaluates (`printed.eval`)
# only what was read, and `own_values` gives the constants the query
# defines, whose printed values must be what their definitions give.

module z3model

import std.list
import std.bytes
import printed
import printed (Names, Def, Defs)
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node)
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, Sig, Context, FunDecl, Defined)
import term (Command, DeclareSort, DeclareDatatypes, DeclareFun, DefineFuns, Assume, Assert)
import model (Value, Truth, Integer, Sequence, Constructed, Element, ArrayElem)
import model (Model, Domain, UpTo, Unsized)

# A definition the model gives, checked, with its rank: it calls only
# definitions of lower rank.
record Printed
    name~Name
    params~List Sort
    result~Sort
    body~printed.Term
    rank~Nat

# What a `(get-model)` printed, read whole: its definitions, and how many
# elements each uninterpreted sort with a universe has.
export record Full
    defs~List Printed
    universes~List (Sort, Nat)

# ── Reading the items ────────────────────────────────────────────────────────

# A `define-fun` as written: its name, parameters, result sort and body.
record Written src : src~Bytes
    name~Name
    params~List (Name, Sort)
    result~Sort
    body~SExpr src

# The items of a `(get-model)` list, sorted.
record Items src : src~Bytes
    defs~List (Written src)
    elements~List (Sort, Nat)
    constraints~List (Sort, List Nat)
    # The cardinality constraints' variables.
    vars~List Name

fn params_from sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List (Name, Sort)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, s] _ :: rest ->
            let sort = try printed.sort_from sig s
            let more = try params_from sig rest
            if list.all (\(m, _) -> m != n) more then Ok ((n, sort) :: more) else Err (b"a definition whose parameters share a name: " ++ n)
        _                                       -> Err b"a parameter that isn't `(NAME SORT)`"

# The element `n` names in `s`, an uninterpreted sort (an instance of one,
# if it has parameters: Z3 spells its elements by the sort's name alone).
fn element_in sig s n -> r : sig~Sig, s~Sort, n~Name, r~Option Nat
    match s
        Unin u _ -> if u < len sig.sorts then printed.element_number sig.sorts[u].name n else None
        _        -> None

fn items_of sig items -> r : sig~Sig, items~List (SExpr src), r~Result (Items src) Bytes
    match items
        []        -> Ok (Items [] [] [] [])
        e :: rest ->
            let f = try items_of sig rest
            match e
                Node [Leaf (Symbol k False) _, Leaf (Symbol n _) _, Node ps _, s, body] _ if k == b"define-fun" ->
                    let params = try params_from sig ps
                    let result = try printed.sort_from sig s
                    Ok (Items (Written n params result body :: f.defs) f.elements f.constraints f.vars)
                Node [Leaf (Symbol k False) _, Leaf (Symbol n _) _, Node [] _, s] _ if k == b"declare-fun" ->
                    let sort = try printed.sort_from sig s
                    match element_in sig sort n
                        Some x -> Ok (Items f.defs ((sort, x) :: f.elements) f.constraints f.vars)
                        None   -> Err (b"a `declare-fun` that isn't an element of an uninterpreted sort: " ++ n)
                Node [Leaf (Symbol k False) _, Node [Node [Leaf (Symbol x _) _, t] _] _, body] _ if k == b"forall" ->
                    let sort = try printed.sort_from sig t
                    let named = try cardinality sig sort x body
                    Ok (Items f.defs f.elements ((sort, named) :: f.constraints) (x :: f.vars))
                _ -> Err b"an item of the model that isn't `define-fun`, `declare-fun` or a cardinality constraint"

# The elements a cardinality constraint over variable `x` of sort `s`
# names: `(= x E)` for one, `(or (= x E1) …)` for more.
fn cardinality sig s x body -> r : sig~Sig, s~Sort, x~Name, body~SExpr src, r~Result (List Nat) Bytes
    match body
        Node (Leaf (Symbol o False) _ :: alts) _ if o == b"or" ->
            if list.length alts >= 2 then alternatives sig s x alts else Err b"a cardinality constraint `or` of fewer than two elements"
        _ -> alternatives sig s x [body]

fn alternatives sig s x es -> r : sig~Sig, s~Sort, x~Name, es~List (SExpr src), r~Result (List Nat) Bytes
    match es
        []        -> Ok []
        e :: rest ->
            let more = try alternatives sig s x rest
            match e
                Node [Leaf (Symbol q False) _, Leaf (Symbol v _) _, Leaf (Symbol n _) _] _ if q == b"=" and v == x ->
                    match element_in sig s n
                        Some k -> Ok (k :: more)
                        None   -> Err (b"a cardinality constraint naming what isn't an element: " ++ n)
                _ -> Err b"a cardinality constraint that isn't `(or (= x E) …)`"

# The elements of sort `s` among `es`.
fn of_sort es s -> r : es~List (Sort, Nat), s~Sort, r~List Nat
    match es
        []             -> []
        (t, k) :: rest -> if t == s then k :: of_sort rest s else of_sort rest s

# The first cardinality constraint variable spelled like a name: an
# element of any sort, a name the query introduces, or one the model
# defines. Such a variable would make the constraint say something else
# (`(= x x)`), so the model is not read.
fn named_var c items -> r : c~Context, items~Items src, r~Option Name
    let taken = query_names c ++ list.map (\d -> d.name) items.defs
    first_taken (term.signature c) taken items.vars

fn first_taken sig taken vs -> r : sig~Sig, taken~List Name, vs~List Name, r~Option Name
    match vs
        []        -> None
        v :: rest -> if list.contains taken v or element_spelling sig v 0 then Some v else first_taken sig taken rest

fn vars_free c items -> r : c~Context, items~Items src, r~Result Nat Bytes
    match named_var c items
        Some v -> Err (b"a cardinality constraint whose variable is spelled like a name: " ++ v)
        None   -> Ok 0

# Whether `n` is spelled like an element of an uninterpreted sort of
# `sig`, from the `u`-th on.
fn element_spelling sig n u -> r : sig~Sig, n~Name, u~Nat, u <= len sig.sorts, r~Bool
    decreasing len sig.sorts - u
    if u >= len sig.sorts then False else printed.element_number sig.sorts[u].name n != None or element_spelling sig n (u + 1)

# Whether `ks` and `ls` hold the same numbers, each once, and they are `0`
# to `n - 1`.
fn exactly ks ls -> r : ks~List Nat, ls~List Nat, r~Bool
    list.unique ks and list.unique ls and list.length ks == list.length ls
        and list.all (\k -> list.contains ls k and k < list.length ks) ks

# Each universe: its sort and size, when its elements and its constraint
# agree exactly, and each sort has at most one constraint.
fn universes es cs -> r : es~List (Sort, Nat), cs~List (Sort, List Nat), r~Result (List (Sort, Nat)) Bytes
    match cs
        []              -> if es == [] then Ok [] else Err b"an element declared without a cardinality constraint"
        (s, ks) :: rest ->
            if list.all (\(t, _) -> t != s) rest
                if exactly (of_sort es s) ks
                    let more = try universes (without es s) rest
                    Ok ((s, list.length ks) :: more)
                else
                    Err b"a universe whose elements and cardinality constraint don't agree, or aren't numbered from 0"
            else
                Err b"two cardinality constraints for one sort"

fn without es s -> r : es~List (Sort, Nat), s~Sort, r~List (Sort, Nat)
    match es
        []             -> []
        (t, k) :: rest -> if t == s then without rest s else (t, k) :: without rest s

# ── Which names a model may define ───────────────────────────────────────────

# Whether the query introduces a name with `!`, as Z3's own names in a
# model have: such a query gets no model read.
export fn bang c -> r : c~Context, r~Bool
    not (list.all (\n -> not (has_bang n 0)) (query_names c))

export let BANG = b"the query introduces a name with `!`, as Z3's own names in a model are"

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

# The assertion names of the query.
fn assertion_names cs -> r : cs~List Command, r~List Name
    match cs
        []                 -> []
        Assert _ n :: rest -> option_name n ++ assertion_names rest
        Assume _ n :: rest -> option_name n ++ assertion_names rest
        _ :: rest          -> assertion_names rest

# The function of `sig` named `n`.
fn query_fun sig n i -> r : sig~Sig, n~Name, i~Nat, i <= len sig.funs, r~Option FunDecl
    decreasing len sig.funs - i
    if i >= len sig.funs then None else if sig.funs[i].name == n then Some sig.funs[i] else query_fun sig n (i + 1)

# Whether the model may define `n` with these sorts: a function or
# constant the query declares, at its sorts; a constant the query defines,
# at its sort; an assertion name, as a `Bool` constant; or one of Z3's own
# (above).
fn may_define c n ps res -> r : c~Context, n~Name, ps~List Sort, res~Sort, r~Bool
    match query_fun (term.signature c) n 0
        Some f -> f.params == ps and f.result == res and (f.kind != Defined or ps == [])
        None   ->
            if list.contains (assertion_names (term.commands c)) n
                ps == [] and res == Bool
            else if n == b"div0" or n == b"mod0"
                ps == [Int, Int] and res == Int
            else if n == b"seq.nth_u"
                ps == [Seq res, Int]
            else
                len n > 2 and bytes.matches_at n 0 b"k!" and printed.canonical (bytes.slice n 2 (len n)) != None

# Whether two of `ds` have one name (and, for `seq.nth_u`, one sort).
fn twice ds -> r : ds~List (Written src), r~Bool
    match ds
        []        -> False
        d :: rest -> not (list.all (\e -> e.name != d.name or (d.name == b"seq.nth_u" and e.params != d.params)) rest) or twice rest

fn first_not_allowed c ds -> r : c~Context, ds~List (Written src), r~Option Name
    match ds
        []        -> None
        d :: rest -> if may_define c d.name (list.map (\(_, t) -> t) d.params) d.result then first_not_allowed c rest else Some d.name

# ── The whole model ──────────────────────────────────────────────────────────

# The model in the items of a `(get-model)` list, for context `c`, read
# whole (see the top of this file), or why it isn't read.
export fn full c items -> r : c~Context, items~List (SExpr src), r~Result Full Bytes
    let sig = term.signature c
    if bang c
        Err BANG
    else
        let its = try items_of sig items
        let us = try universes its.elements its.constraints
        let _ = try vars_free c its
        match first_not_allowed c its.defs
            Some n -> Err (b"a definition of a name the model may not define, or at sorts other than the query's: " ++ n)
            None   ->
                if twice its.defs
                    Err b"two definitions of one name"
                else
                    let names = Names sig (list.map (\d -> Def d.name (list.map (\(_, t) -> t) d.params) d.result) its.defs) us
                    let bodies = try checked_bodies names its.defs
                    let ranks = try ranked bodies
                    Ok (Full (with_ranks its.defs bodies ranks) us)

fn checked_bodies names ds -> r : names~Names, ds~List (Written src), r~Result (List printed.Term) Bytes
    match ds
        []        -> Ok []
        d :: rest ->
            let b = try printed.checked names (list.reverse d.params) d.result d.body
            let more = try checked_bodies names rest
            Ok (b :: more)

fn with_ranks ds bs rs -> r : ds~List (Written src), bs~List printed.Term, rs~List Nat, r~List Printed
    match (ds, bs, rs)
        (d :: dr, b :: br, k :: kr) -> Printed d.name (list.map (\(_, t) -> t) d.params) d.result b k :: with_ranks dr br kr
        _                           -> []

# Each definition's rank: one more than the highest rank of those it
# refers to (0 if none). Each round ranks every definition whose
# references all have ranks; with `n` definitions, `n` rounds rank them
# all, unless some refer to themselves. Rounds give what an order by
# dependencies would, and end by a count the checker sees (`left`); with
# the few definitions a model has (measured: at most a few dozen), the
# `n` rounds cost nothing that matters.
fn ranked bodies -> r : bodies~List printed.Term, r~Result (List Nat) Bytes
    let refs = list.map printed.refs bodies
    let n = list.length bodies
    let rounds = rank_rounds refs (list.map (\_ -> None) refs) n
    if list.all (\x -> x != None) rounds
        Ok (list.map (\x -> or_zero x) rounds)
    else
        Err b"a definition that refers to itself, through others or not"

fn or_zero x -> r : x~Option Nat, r~Nat
    match x
        Some k -> k
        None   -> 0

fn rank_rounds refs known left -> r : refs~List (List Nat), known~List (Option Nat), left~Nat, r~List (Option Nat)
    decreasing left
    if left == 0 then known else rank_rounds refs (list.map (\rs -> rank_of rs known) refs) (left - 1)

# The rank of a definition referring to `rs`, if all of them have one.
fn rank_of rs known -> r : rs~List Nat, known~List (Option Nat), r~Option Nat
    match rs
        []        -> Some 0
        f :: rest ->
            match (list.head (list.drop f known), rank_of rest known)
                (Some (Some k), Some m) -> Some (if k + 1 > m then k + 1 else m)
                _                       -> None

# ── Evaluating ───────────────────────────────────────────────────────────────

# The elements of `Unin u args`: those of its universe, if Z3 printed one;
# else the model doesn't say how many there are.
fn domain_of full u args -> r : full~Full, u~Nat, args~List Sort, r~Domain
    match printed.universe full.universes (Unin u args)
        Some n -> if n > 0 then UpTo (n - 1) else Unsized
        None   -> Unsized

fn defs_of c full -> d : c~Context, full~Full, d~Defs
    Defs (term.signature c) (\u args -> domain_of full u args) (list.map (\p -> (p.rank, p.body)) full.defs)

# The definition named `n` with parameters `ps` and result `res`.
fn find full n ps res -> r : full~Full, n~Name, ps~List Sort, res~Sort, r~Option Printed
    find_in full.defs n ps res

fn find_in ds n ps res -> r : ds~List Printed, n~Name, ps~List Sort, res~Sort, r~Option Printed
    match ds
        []        -> None
        d :: rest -> if d.name == n and d.params == ps and d.result == res then Some d else find_in rest n ps res

fn apply c full p vs -> r : c~Context, full~Full, p~Printed, vs~List Value, r~Option Value
    if list.length vs != list.length p.params
        None
    else
        match printed.eval (defs_of c full) p.rank (list.reverse vs) p.body
            Ok v  -> Some v
            Err _ -> None

fn fun_at c full f vs -> r : c~Context, full~Full, f~Nat, vs~List Value, r~Option Value
    let sig = term.signature c
    if f < len sig.funs and sig.funs[f].kind != Defined
        match find full sig.funs[f].name sig.funs[f].params sig.funs[f].result
            Some p -> apply c full p vs
            None   -> None
    else
        None

fn int_of r -> n : r~Option Value, n~Option Int
    match r
        Some (Integer x) -> Some x
        _                -> None

fn by_zero c full name n -> r : c~Context, full~Full, name~Name, n~Int, r~Option Int
    match find full name [Int, Int] Int
        Some p -> int_of (apply c full p [Integer n, Integer 0])
        None   -> None

# The model `full` describes, for `c`. Selectors of another constructor's
# value are not printed, so the model doesn't say them.
export fn model_of c full fuel -> m : c~Context, full~Full, fuel~Nat, m~Model
    let funs = \f vs -> fun_at c full f vs
    let div_zero = \n -> by_zero c full b"div0" n
    let mod_zero = \n -> by_zero c full b"mod0" n
    let nth = \e xs i ->
        match find full b"seq.nth_u" [Seq e, Int] e
            Some p -> apply c full p [Sequence xs, Integer i]
            None   -> None
    let none5 = \_ _ _ _ _ -> None
    let domain = \u args -> domain_of full u args
    model.normal_arrays (term.signature c) (model.without_arrays funs div_zero mod_zero nth none5 domain fuel)

# What the model printed for the query's own constants (those it
# defines, with no parameters) and for its named assertions: each one's
# name, the query's term for it (the constant, or the assertion), and the
# printed value, if this reader can evaluate it. Where both have values,
# they must be the same. A printed value is used nowhere else: the query's
# definitions are run as their bodies.
export fn own_values c full -> r : c~Context, full~Full, r~List (Name, term.Term, Option Value)
    own_from c (term.signature c) full 0 ++ named_from c full (term.commands c)

fn own_from c sig full f -> r : c~Context, sig~Sig, full~Full, f~Nat, f <= len sig.funs,
                                r~List (Name, term.Term, Option Value)
    decreasing len sig.funs - f
    if f >= len sig.funs
        []
    else
        let more = own_from c sig full (f + 1)
        if sig.funs[f].kind == Defined and sig.funs[f].params == []
            match find full sig.funs[f].name [] sig.funs[f].result
                Some p -> (sig.funs[f].name, term.App (term.Fun f) [], apply c full p []) :: more
                None   -> more
        else
            more

fn named_from c full cs -> r : c~Context, full~Full, cs~List Command, r~List (Name, term.Term, Option Value)
    match cs
        []                        -> []
        Assert t (Some n) :: rest ->
            match find full n [] Bool
                Some p -> (n, t, apply c full p []) :: named_from c full rest
                None   -> named_from c full rest
        _ :: rest                 -> named_from c full rest

# Whether Z3 printed an interpretation of the `f`-th function.
export fn printed_fun sig full f -> r : sig~Sig, full~Full, f~Nat, r~Bool
    f < len sig.funs and has_name full.defs sig.funs[f].name

fn has_name ds n -> r : ds~List Printed, n~Name, r~Bool
    match ds
        []        -> False
        d :: rest -> d.name == n or has_name rest n

# Whether Z3 printed a definition named `n`.
export fn printed_name full n -> r : full~Full, n~Name, r~Bool
    has_name full.defs n
