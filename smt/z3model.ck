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
# A body is evaluated here, at the arguments `smt.model` asks for, by
# `interp`, which knows the forms Z3 prints and nothing else. This reader is
# not trusted: whatever it gives is checked against its sort by
# `smt.model`, and a mistake here can only make an assertion look false or
# undetermined, never make a false model look like a model. `unread` lists
# the forms a model holds that `interp` doesn't know.

module z3model

import std.list
import std.bytes
import answer
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node)
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, Sig, Context)
import model (Value, Truth, Integer, Sequence, Constructed, Element, ConstArray, StoreArray, ModelArray)
import model (Model, Domain, UpTo, Countable)

# A `define-fun` Z3 printed.
record Printed src : src~Bytes
    name~Name
    params~List (Name, Sort)
    result~Sort
    body~SExpr src

# What a `(get-model)` printed: its definitions, the arrays it builds from a
# function or a `lambda` (numbered, for `ModelArray`), and how many elements
# each uninterpreted sort has.
export record Full src : src~Bytes
    defs~List (Printed src)
    arrays~List (SExpr src)
    universes~List (Sort, Nat)

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
fn sort_from sig e -> r : sig~Sig, e~SExpr src, r~Result Sort Bytes
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

# ── Reading the model ────────────────────────────────────────────────────────

fn params_from sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List (Name, Sort)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, s] _ :: rest ->
            let sort = try sort_from sig s
            let more = try params_from sig rest
            Ok ((n, sort) :: more)
        _                                       -> Err b"a parameter that isn't `(NAME SORT)`"

fn bump us n -> r : us~List (Sort, Nat), n~Sort, r~List (Sort, Nat)
    match us
        []             -> [(n, 1)]
        (m, k) :: rest -> if m == n then (m, k + 1) :: rest else (m, k) :: bump rest n

# The model in the items of a `(get-model)` list.
export fn full sig items -> r : sig~Sig, items~List (SExpr src), r~Result (Full src) Bytes
    match items
        []        -> Ok (Full [] [] [])
        e :: rest ->
            let f = try full sig rest
            match e
                Node [Leaf (Symbol k False) _, Leaf (Symbol n _) _, Node ps _, s, body] _ if k == b"define-fun" ->
                    let params = try params_from sig ps
                    let result = try sort_from sig s
                    Ok (Full (Printed n params result body :: f.defs) (lambdas body ++ f.arrays) f.universes)
                Node [Leaf (Symbol k False) _, Leaf (Symbol _ _) _, Node [] _, s] _ if k == b"declare-fun" ->
                    let sort = try sort_from sig s
                    Ok (Full f.defs f.arrays (bump f.universes sort))
                Node (Leaf (Symbol k False) _ :: _) _ if k == b"forall" -> Ok f
                _ -> Err b"an item of the model that isn't `define-fun`, `declare-fun` or a cardinality constraint"

# Every `lambda` and `(_ as-array f)` in `e`, outermost first.
fn lambdas e -> r : e~SExpr src, r~List (SExpr src)
    match e
        Leaf _ _     -> []
        Node [Leaf (Symbol l False) _, _, body] _ if l == b"lambda" -> e :: lambdas body
        Node [Leaf (Symbol u False) _, Leaf (Symbol a False) _, _] _ if u == b"_" and a == b"as-array" -> [e]
        Node items _ -> all_lambdas items

fn all_lambdas es -> r : es~List (SExpr src), r~List (SExpr src)
    match es
        []        -> []
        e :: rest -> lambdas e ++ all_lambdas rest

fn index_of xs x i -> r : xs~List (SExpr src), x~SExpr src, i~Nat, r~Option Nat
    match xs
        []        -> None
        y :: rest -> if y == x then Some i else index_of rest x (i + 1)

fn nth_of xs k -> r : xs~List a, k~Nat, r~Option a
    list.head (list.drop k xs)

fn find_def ds n arity -> r : ds~List (Printed src), n~Name, arity~Nat, r~Option (Printed src)
    match ds
        []        -> None
        d :: rest -> if d.name == n and list.length d.params == arity then Some d else find_def rest n arity

# ── Evaluating what Z3 printed ───────────────────────────────────────────────

let TOO_DEEP = b"Z3's model nests too deep"

# How deep evaluation of the model's bodies may go.
let DEPTH = 100000

type Env = env~List (Name, Value)

fn lookup env n -> r : env~Env, n~Name, r~Option Value
    match env
        []             -> None
        (m, v) :: rest -> if m == n then Some v else lookup rest n

fn ctor_named cs n k -> r : cs~List Ctor, n~Name, k~Nat, r~Option (Nat, Ctor)
    match cs
        []        -> None
        c :: rest -> if c.name == n then Some (k, c) else ctor_named rest n (k + 1)

fn element_of sig s n -> r : sig~Sig, s~Sort, n~Name, r~Option Nat
    match s
        Unin u _ ->
            if u < len sig.sorts
                let prefix = sig.sorts[u].name ++ b"!val!"
                if len n > len prefix and bytes.matches_at n 0 prefix
                    answer.digits_value (bytes.slice n (len prefix) (len n))
                else
                    None
            else
                None
        _        -> None

# The sort `e` has, where it can be told without an expected sort.
fn sort_of_expr sig full env e depth -> r : sig~Sig, full~Full src, env~List (Name, Sort), e~SExpr src, depth~Nat,
                                            r~Option Sort
    decreasing depth
    if depth == 0
        None
    else
        match e
            Leaf (Numeral _) _                       -> Some Int
            Leaf (Symbol n _) _                      ->
                if n == b"true" or n == b"false"
                    Some Bool
                else
                    match var_sort env n
                        Some s -> Some s
                        None   ->
                            match find_def full.defs n 0
                                Some d -> Some d.result
                                None   -> ctor_sort sig n 0
            Node [Leaf (Symbol a False) _, _, s] _ if a == b"as" ->
                match sort_from sig s
                    Ok x  -> Some x
                    Err _ -> None
            Node (Leaf (Symbol n False) _ :: args) _ ->
                if n == b"+" or n == b"-" or n == b"*" or n == b"div" or n == b"mod" or n == b"seq.len"
                    Some Int
                else if n == b"<" or n == b"<=" or n == b">" or n == b">=" or n == b"=" or n == b"and" or n == b"or"
                    or n == b"not" or n == b"=>"
                    Some Bool
                else if n == b"ite"
                    match args
                        [_, a, b] ->
                            match sort_of_expr sig full env a (depth - 1)
                                Some s -> Some s
                                None   -> sort_of_expr sig full env b (depth - 1)
                        _         -> None
                else if n == b"seq.unit"
                    match args
                        [a] ->
                            match sort_of_expr sig full env a (depth - 1)
                                Some s -> Some (Seq s)
                                None   -> None
                        _   -> None
                else if n == b"seq.++" or n == b"store"
                    match args
                        a :: _ -> sort_of_expr sig full env a (depth - 1)
                        []     -> None
                else if n == b"select"
                    match args
                        [a, _] ->
                            match sort_of_expr sig full env a (depth - 1)
                                Some (Arr _ v) -> Some v
                                _              -> None
                        _      -> None
                else
                    match find_def full.defs n (list.length args)
                        Some d -> Some d.result
                        None   -> ctor_sort sig n 0
            Node (Node [Leaf (Symbol a False) _, _, s] _ :: _) _ if a == b"as" ->
                match sort_from sig s
                    Ok x  -> Some x
                    Err _ -> None
            _                                        -> None

# The sort of constructor `n`'s values, if its datatype has no parameters.
fn ctor_sort sig n d -> r : sig~Sig, n~Name, d~Nat, d <= len sig.datatypes, r~Option Sort
    decreasing len sig.datatypes - d
    if d >= len sig.datatypes
        None
    else if sig.datatypes[d].params == [] and ctor_named sig.datatypes[d].ctors n 0 != None
        Some (Data d [])
    else
        ctor_sort sig n (d + 1)

fn var_sort env n -> r : env~List (Name, Sort), n~Name, r~Option Sort
    match env
        []             -> None
        (m, s) :: rest -> if m == n then Some s else var_sort rest n

fn sort_env env -> r : env~List (Name, Value, Sort), r~List (Name, Sort)
    match env
        []                -> []
        (n, _, s) :: rest -> (n, s) :: sort_env rest

fn value_env env -> r : env~List (Name, Value, Sort), r~Env
    match env
        []                -> []
        (n, v, _) :: rest -> (n, v) :: value_env rest

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

# The value of `e`, of sort `s`, where `env` gives the parameters' values
# and sorts.
fn interp sig full env lets s e depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), s~Sort, e~SExpr src,
                                             depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let d = depth - 1
        match e
            Leaf (Symbol n _) _                      ->
                match (find_let lets n, lookup (value_env env) n)
                    (Some b, _)    -> interp sig full env lets s b d
                    (None, Some v) -> Ok v
                    (None, None)   ->
                        match find_def full.defs n 0
                            Some p -> interp sig full [] [] p.result p.body d
                            None   ->
                                match element_of sig s n
                                    Some k -> Ok (Element k)
                                    None   -> answer.value_from sig s e [] d
            Leaf _ _                                 -> answer.value_from sig s e [] d
            Node [Leaf (Symbol l False) _, _, _] _ if l == b"lambda" -> array_ref full s e
            Node [Leaf (Symbol u False) _, Leaf (Symbol a False) _, _] _ if u == b"_" and a == b"as-array" ->
                array_ref full s e
            Node [Leaf (Symbol m False) _, Leaf (Numeral n) _] _ if m == b"-" -> Ok (Integer (0 - n))
            Node [Leaf (Symbol a False) _, _, _] _ if a == b"as" -> answer.value_from sig s e [] d
            Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
                let more = try let_binds binds
                interp sig full env (list.reverse more ++ lets) s body d
            Node (Leaf (Symbol n False) _ :: args) _ -> call sig full env lets s n args d
            Node (Node [Leaf (Symbol a False) _, Leaf (Symbol c _) _, _] _ :: args) _ if a == b"as" ->
                if c == b"const"
                    match (s, args)
                        (Arr i v, [x]) ->
                            let w = try interp sig full env lets v x d
                            Ok (ConstArray i w)
                        _              -> Err b"a constant array where the sort isn't an array"
                else
                    construct sig full env lets s c args d
            _                                        -> answer.value_from sig s e [] d

fn find_let lets n -> r : lets~List (Name, SExpr src), n~Name, r~Option (SExpr src)
    match lets
        []             -> None
        (m, e) :: rest -> if m == n then Some e else find_let rest n

fn let_binds es -> r : es~List (SExpr src), r~Result (List (Name, SExpr src)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, e] _ :: rest ->
            let more = try let_binds rest
            Ok ((n, e) :: more)
        _                                       -> Err b"a `let` binding that isn't `(NAME VALUE)`"

fn array_ref full s e -> r : full~Full src, s~Sort, e~SExpr src, r~Result Value Bytes
    match index_of full.arrays e 0
        Some k -> Ok (ModelArray s k)
        None   -> Err b"an array this reader didn't number"

# `n` applied to `args`.
fn call sig full env lets s n args depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), s~Sort, n~Name,
                                                args~List (SExpr src), depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        let d = depth - 1
        let senv = sort_env env
        let bool = \x -> as_bool (interp sig full env lets Bool x d)
        let int = \x -> as_int (interp sig full env lets Int x d)
        match (n, args)
            (_, [c, a, b]) if n == b"ite" ->
                let cv = try bool c
                if cv then interp sig full env lets s a d else interp sig full env lets s b d
            (_, [a]) if n == b"not" ->
                let x = try bool a
                Ok (Truth (not x))
            (_, _) if n == b"and" -> conj sig full env lets args d
            (_, _) if n == b"or" -> disj sig full env lets args d
            (_, [a, b]) if n == b"=>" ->
                let x = try bool a
                let y = try bool b
                Ok (Truth (not x or y))
            (_, [a, b]) if n == b"=" ->
                let sort =
                    match sort_of_expr sig full senv a d
                        Some x -> Some x
                        None   -> sort_of_expr sig full senv b d
                match sort
                    Some t ->
                        let x = try interp sig full env lets t a d
                        let y = try interp sig full env lets t b d
                        if model.plain x and model.plain y then Ok (Truth (x == y)) else Err b"`=` of arrays"
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
                        let x = try interp sig full env lets el a d
                        Ok (Sequence [x])
                    _      -> Err b"seq.unit where the sort isn't a sequence"
            (_, _) if n == b"seq.++" -> concat sig full env lets s args d
            (_, [a, i, v]) if n == b"store" ->
                match s
                    Arr is vs ->
                        let x = try interp sig full env lets s a d
                        let j = try interp sig full env lets is i d
                        let w = try interp sig full env lets vs v d
                        Ok (StoreArray x j w)
                    _         -> Err b"store where the sort isn't an array"
            _ ->
                match find_def full.defs n (list.length args)
                    Some p ->
                        let vs = try interp_all sig full env lets (list.map (\(_, t) -> t) p.params) args d
                        interp sig full (bind p.params vs) [] p.result p.body d
                    None   -> construct sig full env lets s n args d

fn bind ps vs -> r : ps~List (Name, Sort), vs~List Value, r~List (Name, Value, Sort)
    match (ps, vs)
        ((n, s) :: pr, v :: vr) -> (n, v, s) :: bind pr vr
        _                       -> []

fn arith rx ry f -> r : rx~Result Int Bytes, ry~Result Int Bytes, f~(Int -> Int -> Result Value Bytes),
                        r~Result Value Bytes
    let x = try rx
    let y = try ry
    f x y

fn conj sig full env lets args depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), args~List (SExpr src),
                                            depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match args
            []        -> Ok (Truth True)
            a :: rest ->
                match interp sig full env lets Bool a (depth - 1)
                    Ok (Truth False) -> Ok (Truth False)
                    Ok (Truth True)  -> conj sig full env lets rest (depth - 1)
                    Ok _             -> Err b"not a Bool"
                    Err e            -> Err e

fn disj sig full env lets args depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), args~List (SExpr src),
                                            depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match args
            []        -> Ok (Truth False)
            a :: rest ->
                match interp sig full env lets Bool a (depth - 1)
                    Ok (Truth True)  -> Ok (Truth True)
                    Ok (Truth False) -> disj sig full env lets rest (depth - 1)
                    Ok _             -> Err b"not a Bool"
                    Err e            -> Err e

fn concat sig full env lets s args depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), s~Sort,
                                                args~List (SExpr src), depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match args
            []        -> Ok (Sequence [])
            a :: rest ->
                let x = try interp sig full env lets s a (depth - 1)
                let y = try concat sig full env lets s rest (depth - 1)
                match (x, y)
                    (Sequence xs, Sequence ys) -> Ok (Sequence (xs ++ ys))
                    _                          -> Err b"seq.++ of something that isn't a sequence"

fn interp_all sig full env lets ss es depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), ss~List Sort,
                                                   es~List (SExpr src), depth~Nat, r~Result (List Value) Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match (ss, es)
            ([], [])           -> Ok []
            (s :: sr, e :: er) ->
                let v = try interp sig full env lets s e (depth - 1)
                let vs = try interp_all sig full env lets sr er (depth - 1)
                Ok (v :: vs)
            _                  -> Err b"a call with the wrong number of arguments"

# Constructor `n` of `s` applied to `args`.
fn construct sig full env lets s n args depth -> r : sig~Sig, full~Full src, env~List (Name, Value, Sort), lets~List (Name, SExpr src), s~Sort,
                                                     n~Name, args~List (SExpr src), depth~Nat, r~Result Value Bytes
    decreasing depth
    if depth == 0
        Err TOO_DEEP
    else
        match s
            Data d sargs ->
                if d < len sig.datatypes
                    match ctor_named sig.datatypes[d].ctors n 0
                        Some (k, c) ->
                            let ss = list.map (term.instantiate sargs) (term.field_sorts c.fields)
                            let fs = try interp_all sig full env lets ss args (depth - 1)
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
        match interp sig full (bind d.params vs) [] d.result d.body DEPTH
            Ok v  -> Some v
            Err _ -> None

# The `k`-th array of the model at index `i`.
fn array_at sig full k i -> r : sig~Sig, full~Full src, k~Nat, i~Value, r~Option Value
    match nth_of full.arrays k
        Some (Node [Leaf (Symbol _ _) _, Node [Node [Leaf (Symbol v _) _, s] _] _, body] _) ->
            match (sort_from sig s, sort_of_expr sig full [] body DEPTH)
                (Ok vs, Some rs) ->
                    match interp sig full [(v, i, vs)] [] rs body DEPTH
                        Ok x  -> Some x
                        Err _ -> None
                _                -> None
        Some (Node [_, _, Leaf (Symbol f _) _] _)                                           ->
            match find_def full.defs f 1
                Some d -> apply_def sig full d [i]
                None   -> None
        _                                                                                   -> None

# The `seq.nth_u` for sequences of `e`.
fn nth_def ds e -> r : ds~List (Printed src), e~Sort, r~Option (Printed src)
    match ds
        []        -> None
        d :: rest ->
            match d.params
                [(_, Seq x), (_, Int)] if d.name == b"seq.nth_u" and x == e -> Some d
                _ -> nth_def rest e

# The elements Z3 printed for `Unin u args`; a sort it printed none for
# appears in no term, and is taken as countable.
fn domain_of full u args -> r : full~Full src, u~Nat, args~List Sort, r~Domain
    match universe full.universes (Unin u args)
        Some n -> if n > 0 then UpTo (n - 1) else Countable
        None   -> Countable

fn universe us s -> r : us~List (Sort, Nat), s~Sort, r~Option Nat
    match us
        []             -> None
        (t, k) :: rest -> if t == s then Some k else universe rest s

fn fun_at sig full f vs -> r : sig~Sig, full~Full src, f~Nat, vs~List Value, r~Option Value
    if f < len sig.funs
        match find_def full.defs sig.funs[f].name (list.length vs)
            Some d -> apply_def sig full d vs
            None   -> None
    else
        None

fn int_of r -> n : r~Option Value, n~Option Int
    match r
        Some (Integer x) -> Some x
        _                -> None

fn by_zero sig full name n -> r : sig~Sig, full~Full src, name~Name, n~Int, r~Option Int
    match find_def full.defs name 2
        Some d -> int_of (apply_def sig full d [Integer n, Integer 0])
        None   -> None

# The model `full` describes, for `c`. Selectors of another constructor's
# value are not printed, so the model doesn't say them.
export fn model_of c full fuel -> m : c~Context, full~Full src, fuel~Nat, m~Model
    let sig = term.signature c
    let funs = \f vs -> fun_at sig full f vs
    let arrays = \_ k i -> array_at sig full k i
    let div_zero = \n -> by_zero sig full b"div0" n
    let mod_zero = \n -> by_zero sig full b"mod0" n
    let nth = \e xs i ->
        match nth_def full.defs e
            Some d -> apply_def sig full d [Sequence xs, Integer i]
            None   -> None
    let none5 = \_ _ _ _ _ -> None
    let domain = \u args -> domain_of full u args
    Model funs arrays div_zero mod_zero nth none5 domain fuel

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
