# model.ck — what a term means in a model: `eval`, `holds`, `fails`.
#
# This module is the definition every answer of the solver is checked
# against (#72, design 1). It is written to be read, not to be fast: each
# operation says what it computes, and where SMT-LIB leaves a result
# unspecified, the model says what it is.
#
# **A model is an SMT-LIB structure.** Every sort is a set of elements and
# every symbol a function of them. An uninterpreted sort's elements are
# `Element n`; an array sort's are `ArrayElem s id`, as in SMT-LIB's
# `ArraysEx`, whose array sorts are sets of elements of the structure (2.6,
# §5.3). The model says what every operation that makes an array gives:
# `const`, `store`, `map +` (`sum`) and `lambda`, and what `select` reads.
# Two arrays are equal exactly when they are the same element, so equality
# is decided for every pair of values, and a model's function may take
# arrays. What makes these SMT-LIB's arrays (read over write, extensionality
# and the rest) is not computed here: `arrays_ok` below states it, for a
# theorem to take as its premises.
#
# **Three answers.** Evaluating a term gives its value, or `Unknown` with a
# reason: the model doesn't say (a partial model, such as the values Z3
# printed), evaluation ran out of fuel, or the model gave a value of the
# wrong sort. `holds c m t` is true only when `t` evaluates to true, and
# `fails c m t` only when it evaluates to false; when neither, nothing is
# claimed. A definite answer is always the term's value in the structure
# the model describes.
#
# **Connectives are Kleene's.** `and` is false as soon as one argument is
# false, whatever the others are, and true only if all are true; `or`
# dually; `=>` is `(not a) or b`. This is exact: every term has a value in
# every structure, so a conjunction with a false argument is false whatever
# the unknown arguments' values are. `ite` evaluates its condition, then
# only the branch it chooses.
#
# **Terms of the context only.** `eval` and `eval_unfolding` evaluate a term
# only if it has a sort in the context with no variables free, `holds_at`
# an axiom only if it is one of the context's (`term.axiom_ok`), and
# `refutes` a goal only if it is a closed `Bool` term of it (`term.fact_ok`); anything
# else is `IllSorted`, or not held.
#
# **Two modes.** `eval`, `holds`, `fails`, `holds_all` and `holds_at` are the
# meaning: every function, defined ones included, is what `Model.funs` says,
# a `lambda` is the array `Model.lambda` names, and a definition's equation
# is a fact like any other (SMT-LIB defines `define-fun-rec` as a declared
# function and its universally quantified equation). The meaning evaluates
# no body, so it needs no fuel: it goes by the structure of the term.
#
# `refutes`, which `Answer.Invalid` uses, evaluates instead with each
# definition marked terminating (`Def.terminates`) run as its own body
# (design 3), within `Model.fuel` levels (past them, `OutOfFuel`): a
# terminating definition's equation then holds by construction wherever
# evaluation finishes, because it has exactly one solution. `refutes`
# requires every definition of the context to be marked: one that isn't may
# have no solution at all (`g x = g x + 1`), and then no model satisfies the
# context, whether or not an assertion calls it (SMT-LIB 2.6, §4.2.3, note
# 4). Z3 5.3.3 answers `sat` to such a context; this module does not follow
# it there. Unfolding a definition not marked terminating is
# `NotTerminating`. In the meaning, a model satisfies definition `d` when it
# satisfies `definition_axiom n d` at all values (`holds_at`).
#
# **`refutes` builds its arrays.** It can't take `arrays_ok` on trust, so it
# evaluates in `normal_arrays sig m`: the same model with arrays named by a
# normal form (a constant and the stores that differ from it, in order),
# so that two arrays are the same element exactly when they are the same
# function. Every constant array has one; stores have one at `Bool`, at a
# domain the model lists, and at sorts this module can show unbounded
# (`Int`, sequences, a countable domain, arrays of those), but not at a
# datatype, which may be finite (`NotGiven`). Z3 prints some arrays with no
# normal form (a `lambda` over a range): those stay `Named`, read through
# what Z3 printed. A `lambda` is read by running its body, within the fuel.
# Comparing two different arrays where one holds a `Named` array or a
# `lambda` is `ArraysCompared`.

# **Quantified axioms.** `holds_at c m a vs` evaluates the body of axiom `a`
# at the values `vs`. A `forall` over an infinite sort can't be evaluated, so
# `refutes` is false for a context with any axiom, patterned or not (an
# `Axiom` with `patterns = []` is a fact like the others, #82): a model is
# never shown to satisfy one, so a query with one is never `Invalid`.
#
# **What a `Model` can't represent** (for #85, model limits). A `Model` is a
# Checkers value, so its functions are computable, and its domains are
# countable (`Element n`, `ArrayElem s (Named k)`). Every first-order
# structure has a countable elementary substructure, which covers arrays
# too, since `ArraysEx` with extensionality is first-order; computability is
# the limit this module adds.

module model

import std.list
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, FunDecl, Def, Axiom, Context, Sig)
import term (Witness, WTrue, WZero, WEmpty, WElement, WConst, WParam, WCon, WOf)
import term (Op, Not, And, Or, Implies, Ite, Eq, Add, Sub, Neg, Mul, Div, Mod, Lt, Le, Gt, Ge, Select, Store, MapAdd)
import term (SeqLen, SeqNth, SeqUnit, SeqConcat, SeqExtract)
import term (Head, Fun, Con, Is, Sel, Num, Boolean, Prim, ConstArr, EmptySeq, Term, Var, App, Let, Lam)

# ── Values ───────────────────────────────────────────────────────────────────

# A value of some sort. A value doesn't record its sort: the term it is the
# value of has one, and `of_sort` says whether a value given by a model
# belongs to a sort.
#
# - `Truth b`, `Integer n`: a `Bool`, an `Int`.
# - `Sequence xs`: a `Seq`, its elements in order.
# - `Constructed k fields`: a datatype's value built by its `k`-th
#   constructor.
# - `Element n`: the `n`-th element of an uninterpreted sort (`declare-sort`).
#   Elements with different numbers are different.
# - `ArrayElem s id`: the element `id` of array sort `s`. Elements with
#   different `id`s are different.
export enum Value
    Truth b              : b~Bool
    Integer n            : n~Int
    Sequence xs          : xs~List Value
    Constructed k fields : k~Nat, fields~List Value
    Element n            : n~Nat
    ArrayElem s id       : s~Sort, id~ArrayId

# Which element of an array sort: the model's `k`-th (`Named k`), or the
# one a normal form names (`Normal base stores`: `base` everywhere except at
# the indices of `stores`). In the meaning both are names and nothing more;
# `normal_arrays` gives `Normal` ones their meaning as functions. `Closure`
# is a `lambda` in `refutes`, read by evaluating its body (the values and
# sorts of the variables around it, and the sort of its own); no model
# gives one.
export enum ArrayId
    Named k                    : k~Nat
    Normal base stores         : base~Value, stores~List (Value, Value)
    Closure env senv sort body : env~List (Result Value Unknown), senv~List Sort, sort~Sort, body~Term

# Why a term has no value here.
export enum Unknown
    # The model doesn't say: what `h` gives at these arguments (`Fun f` for
    # a function; `Prim Div` or `Prim Mod` for a division by zero; `Prim
    # SeqNth` for an index out of range; `Sel d k j` for a selector applied
    # to another constructor's value; `Prim Select`, `Prim Store`, `Prim
    # MapAdd` or `ConstArr s` for an array).
    NotGiven h : h~Head
    # The model doesn't say which array a `lambda` is.
    LambdaNotGiven
    # Evaluation needed more than `Model.fuel` levels (in `refutes` only).
    OutOfFuel
    # Two arrays compared where one is an array Z3 printed without a normal
    # form, or a `lambda` (in `refutes` only).
    ArraysCompared
    # A call of a definition not marked terminating, in `refutes`.
    NotTerminating
    # The model gave a value that isn't of the sort needed.
    WrongSort
    # The term isn't a term of the context. Never for one that is.
    IllSorted

# The elements of an uninterpreted or array sort: `UpTo n` is element 0 to
# element `n` (never empty, as SMT-LIB requires); `Countable` is every
# element. Countable domains are all that is needed (Löwenheim–Skolem, see
# the module's comment). Every `Model` here is a Checkers value, so its
# functions are computable: "every model" in this module means every such
# one.
export enum Domain
    UpTo n : n~Nat
    Countable

# An interpretation of a context's symbols, and of what SMT-LIB leaves
# unspecified. Each function may answer `None`: then the model doesn't say,
# and a term that needs it is `NotGiven`. A model that answers `Some`
# everywhere is complete.
#
# - `funs f vs`: the `f`-th function at arguments `vs`; a constant at `[]`.
# - `select s id i`: element `id` of array sort `s` at index `i`.
# - `const s v`: the element of array sort `s` that is `v` everywhere.
# - `store s id i v`: the element that is `id` with index `i` mapped to `v`.
# - `sum s a b`: the element that is `(_ map (+ (Int Int) Int))` of `a`
#   and `b`.
# - `lambda s env senv x body`: the element that is a `lambda` over a
#   variable of sort `x`, with the variables bound around it having the
#   values `env` (`Var 0` first) and the sorts `senv`.
# - `array_domain s`: the `Named` elements of array sort `s`.
# - `differ s a b`: an index where elements `a` and `b` of `s` differ (for
#   extensionality: `arrays_ok`).
# - `div_zero n`, `mod_zero n`: `(div n 0)` and `(mod n 0)`. SMT-LIB leaves
#   them unspecified; each is a function of `n`, and the two are unrelated.
# - `nth_out e xs i`: `(seq.nth xs i)` for `i` outside `xs`, where the
#   elements are of sort `e`: a function of `xs` and `i`.
# - `wrong_sel d k j args v`: selector `j` of constructor `k` of datatype
#   `d` (at sort arguments `args`) applied to `v`, built by another
#   constructor: a function of `v`.
# - `domain u args`: the elements of `Unin u args`.
# - `fuel`: how many levels `refutes` may unfold definitions (see the
#   module's comment).
#
# What a model gives is checked against the sort needed (`of_sort`), so a
# model can't make a term take a value outside its sort.
export record Model
    funs~(Nat -> List Value -> Option Value)
    select~(Sort -> ArrayId -> Value -> Option Value)
    const~(Sort -> Value -> Option ArrayId)
    store~(Sort -> ArrayId -> Value -> Value -> Option ArrayId)
    sum~(Sort -> ArrayId -> ArrayId -> Option ArrayId)
    lambda~(Sort -> List Value -> List Sort -> Sort -> Term -> Option ArrayId)
    array_domain~(Sort -> Domain)
    differ~(Sort -> ArrayId -> ArrayId -> Value)
    div_zero~(Int -> Option Int)
    mod_zero~(Int -> Option Int)
    nth_out~(Sort -> List Value -> Int -> Option Value)
    wrong_sel~(Nat -> Nat -> Nat -> List Sort -> Value -> Option Value)
    domain~(Nat -> List Sort -> Domain)
    fuel~Nat

# A model whose functions and unspecified results are those given, which
# says nothing about arrays: every array question is `NotGiven`.
export fn without_arrays funs div_zero mod_zero nth_out wrong_sel domain fuel -> m : funs~(Nat -> List Value -> Option Value),
                                                                                     div_zero~(Int -> Option Int),
                                                                                     mod_zero~(Int -> Option Int),
                                                                                     nth_out~(Sort -> List Value -> Int -> Option Value),
                                                                                     wrong_sel~(Nat -> Nat -> Nat -> List Sort -> Value -> Option Value),
                                                                                     domain~(Nat -> List Sort -> Domain), fuel~Nat,
                                                                                     m~Model
    let select = \_ _ _ -> None
    let const = \_ _ -> None
    let store = \_ _ _ _ -> None
    let sum = \_ _ _ -> None
    let lambda = \_ _ _ _ _ -> None
    let differ = \_ _ _ -> Truth False
    Model funs select const store sum lambda (\_ -> Countable) differ div_zero mod_zero nth_out wrong_sel domain fuel

# ── Sorts of values ──────────────────────────────────────────────────────────

fn in_domain d n -> r : d~Domain, n~Nat, r~Bool
    match d
        UpTo last -> n <= last
        Countable -> True

# Whether `v`, given by the model, is a value of sort `s`. An array is one
# of the model's elements of its sort, or a normal form of its sort.
export fn of_sort c m s v -> r : c~Context, m~Model, s~Sort, v~Value, r~Bool
    match (s, v)
        (Bool, Truth _)                 -> True
        (Int, Integer _)                -> True
        (Seq e, Sequence xs)            -> all_of_sort c m e xs
        (Arr i w, ArrayElem t id)       -> t == s and array_of_sort c m s i w id
        (Data d args, Constructed k fs) ->
            match term.ctor (term.signature c) d k
                Some k_ctor -> fields_of_sort c m (list.map (term.instantiate args) (term.field_sorts k_ctor.fields)) fs
                None        -> False
        (Unin u args, Element n)        -> in_domain (m.domain u args) n
        _                               -> False

fn array_of_sort c m s i w id -> r : c~Context, m~Model, s~Sort, i~Sort, w~Sort, id~ArrayId, r~Bool
    match id
        Named k         -> in_domain (m.array_domain s) k
        Normal b st     -> of_sort c m w b and stores_of_sort c m i w st and canonical (term.signature c) m.domain i b st
        Closure _ _ _ _ -> False

fn all_of_sort c m s vs -> r : c~Context, m~Model, s~Sort, vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> of_sort c m s v and all_of_sort c m s rest

fn fields_of_sort c m ss vs -> r : c~Context, m~Model, ss~List Sort, vs~List Value, r~Bool
    match (ss, vs)
        ([], [])           -> True
        (s :: sr, v :: vr) -> of_sort c m s v and fields_of_sort c m sr vr
        _                  -> False

fn stores_of_sort c m i w st -> r : c~Context, m~Model, i~Sort, w~Sort, st~List (Value, Value), r~Bool
    match st
        []             -> True
        (j, x) :: rest -> of_sort c m i j and of_sort c m w x and stores_of_sort c m i w rest

# What the model said, `got`, for a term of sort `s` that needs `h`.
fn given c m s h got -> r : c~Context, m~Model, s~Sort, h~Head, got~Option Value, r~Result Value Unknown
    match got
        None   -> Err (NotGiven h)
        Some v -> if of_sort c m s v then Ok v else Err WrongSort

# The element of array sort `s` the model named, `got`; `missing` if none.
fn given_array c m s missing got -> r : c~Context, m~Model, s~Sort, missing~Unknown, got~Option ArrayId,
                                        r~Result Value Unknown
    match got
        None    -> Err missing
        Some id -> if of_sort c m s (ArrayElem s id) then Ok (ArrayElem s id) else Err WrongSort

# Whether `v` holds no `Named` array: no array Z3 printed without a normal
# form. Two such values built by `normal_arrays` are the same function
# exactly when they are equal as data.
export fn pure v -> r : v~Value, r~Bool
    match v
        Sequence xs                   -> all_pure xs
        Constructed _ fs              -> all_pure fs
        ArrayElem _ (Named _)         -> False
        ArrayElem _ (Closure _ _ _ _) -> False
        ArrayElem _ (Normal b st)     -> pure b and stores_pure st
        _                             -> True

fn all_pure vs -> r : vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> pure v and all_pure rest

fn stores_pure st -> r : st~List (Value, Value), r~Bool
    match st
        []             -> True
        (j, x) :: rest -> pure j and pure x and stores_pure rest

# ── A value of every sort ────────────────────────────────────────────────────
# Every sort of a context has a value: that is what accepting a datatype
# rests on (`term.fits`). `value_of` writes one: for a datatype, its kept
# witness (`Sig.values`) at values of its arguments; for an uninterpreted
# sort, `Element 0`, which every domain has; for an array sort, the
# constant array of a value of its element sort.

# A value of sort `s` (with no `Param` in it), if `sig` has one.
export fn value_of sig s -> r : sig~Sig, s~Sort, r~Option Value
    match s
        Bool        -> Some (Truth True)
        Int         -> Some (Integer 0)
        Seq _       -> Some (Sequence [])
        Unin _ _    -> Some (Element 0)
        Arr _ w     ->
            match value_of sig w
                Some v -> Some (ArrayElem s (Normal v []))
                None   -> None
        Data d args ->
            match values_of sig args
                Some vs -> kept_at sig d args vs
                None    -> None
        Param _     -> None

fn values_of sig ss -> r : sig~Sig, ss~List Sort, r~Option (List Value)
    match ss
        []        -> Some []
        s :: rest ->
            match (value_of sig s, values_of sig rest)
                (Some v, Some vs) -> Some (v :: vs)
                _                 -> None

# Witness `w` of a value of template sort `t` (whose `Param k` is `args`'
# `k`-th sort), where `WParam k` is `vs`' `k`-th value; it is part of
# datatype `d`'s kept witness, so a `WOf e` in it has `e < d`.
fn witness_value sig d args vs w t -> r : sig~Sig, d~Nat, args~List Sort, vs~List Value, w~Witness, t~Sort, r~Option Value
    decreasing (d, witness_size w)
    match (w, t)
        (WTrue, Bool)             -> Some (Truth True)
        (WZero, Int)              -> Some (Integer 0)
        (WEmpty, Seq _)           -> Some (Sequence [])
        (WElement, Unin _ _)      -> Some (Element 0)
        (WConst v, Arr _ e)       ->
            match witness_value sig d args vs v e
                Some x -> Some (ArrayElem (term.instantiate args t) (Normal x []))
                None   -> None
        (WParam k, Param _)       -> list.head (list.drop k vs)
        (WCon k fs, Data e targs) ->
            match term.ctor sig e k
                Some c ->
                    match witness_values sig d args vs fs (list.map (term.instantiate targs) (term.field_sorts c.fields))
                        Some xs -> Some (Constructed k xs)
                        None    -> None
                None   -> None
        (WOf e ws, Data _ targs)  ->
            if e < d
                match witness_values sig d args vs ws targs
                    Some xs -> kept_at sig e (list.map (term.instantiate args) targs) xs
                    None    -> None
            else
                None
        _                         -> None

fn witness_values sig d args vs ws ts -> r : sig~Sig, d~Nat, args~List Sort, vs~List Value, ws~List Witness, ts~List Sort,
                                             r~Option (List Value)
    decreasing (d, witnesses_size ws)
    match (ws, ts)
        ([], [])           -> Some []
        (w :: wr, t :: tr) ->
            match (witness_value sig d args vs w t, witness_values sig d args vs wr tr)
                (Some x, Some xs) -> Some (x :: xs)
                _                 -> None
        _                  -> None

# Datatype `e`'s kept witness at arguments `args`, whose values are `vs`
# (from inside a witness, `e` is before the datatype the witness belongs
# to).
fn kept_at sig e args vs -> r : sig~Sig, e~Nat, args~List Sort, vs~List Value, r~Option Value
    decreasing (e, witness_size (if e < len sig.values then sig.values[e] else WTrue) + 1)
    if e < len sig.values and e < len sig.datatypes
        witness_value sig e args vs sig.values[e] (Data e (term.params_of (list.length sig.datatypes[e].params) 0))
    else
        None

fn witness_size w -> n : w~Witness, n~Nat
    match w
        WConst v  -> 1 + witness_size v
        WCon _ fs -> 1 + witnesses_size fs
        WOf _ ws  -> 1 + witnesses_size ws
        _         -> 1

fn witnesses_size ws -> n : ws~List Witness, n~Nat
    match ws
        []        -> 1
        w :: rest -> 1 + witness_size w + witnesses_size rest

# ── Normal forms ─────────────────────────────────────────────────────────────
# An array is named by one normal form: its constant `base` and the stores
# that differ from it, each index once, in order (`before`). How depends on
# the index sort (`index_kind`), given the model's domains:
#
# - `Listed es`, a finite sort whose elements are `es` (`Bool`, an
#   uninterpreted sort with `UpTo n`): the base is the value at the first of
#   `es`, and stores are at the others;
# - `Unbounded`, a sort this module can write a value of outside any finite
#   set (`fresh`): `Int`, `(Seq e)` for any `e` with a value (`value_of`),
#   an uninterpreted sort with `Countable` elements, `(Array i w)` with `w`
#   unbounded; stores anywhere;
# - `Opaque`, a datatype or any other sort: only constant arrays are named.
#
# Two normal forms are equal exactly when the arrays are the same function:
# if their bases differ, they differ at the first listed element, at an
# index stored in neither (`fresh`), or, for constant arrays, anywhere (no
# sort is empty); if their bases agree, at a stored index.

# How normal forms are made at an index sort.
enum Kind
    Listed es : es~List Value
    Unbounded
    Opaque

fn index_kind sig dom i -> k : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, k~Kind
    match i
        Bool        -> Listed [Truth False, Truth True]
        Unin u args ->
            match dom u args
                UpTo n    -> Listed (elements_upto n)
                Countable -> Unbounded
        _           -> if unbounded sig dom i then Unbounded else Opaque

# `Element 0`, …, `Element n`.
fn elements_upto n -> es : n~Nat, es~List Value
    elements_from 0 (n + 1)

fn elements_from k count -> es : k~Nat, count~Nat, es~List Value
    if count == 0 then [] else Element k :: elements_from (k + 1) (count - 1)

# Whether this module can write a value of `s` outside any finite set.
fn unbounded sig dom s -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, r~Bool
    match s
        Int         -> True
        Seq e       -> value_of sig e != None
        Unin u args -> dom u args == Countable
        Arr _ w     -> unbounded sig dom w
        _           -> False

# A strict total order on values without `Named` arrays (and, for arrays,
# of one sort): by constructor, then by contents.
fn before a b -> r : a~Value, b~Value, r~Bool
    match (a, b)
        (Truth x, Truth y)                   -> not x and y
        (Integer x, Integer y)               -> x < y
        (Sequence xs, Sequence ys)           -> all_before xs ys
        (Constructed k xs, Constructed l ys) -> k < l or (k == l and all_before xs ys)
        (Element x, Element y)               -> x < y
        (ArrayElem _ p, ArrayElem _ q)       -> id_before p q
        _                                    -> rank a < rank b

fn rank v -> r : v~Value, r~Nat
    match v
        Truth _         -> 0
        Integer _       -> 1
        Sequence _      -> 2
        Constructed _ _ -> 3
        Element _       -> 4
        ArrayElem _ _   -> 5

# Lists compared element by element, a shorter one first when it is a
# prefix of the other.
fn all_before xs ys -> r : xs~List Value, ys~List Value, r~Bool
    match (xs, ys)
        ([], [])           -> False
        ([], _)            -> True
        (_, [])            -> False
        (x :: xr, y :: yr) -> before x y or (x == y and all_before xr yr)

fn id_before p q -> r : p~ArrayId, q~ArrayId, r~Bool
    match (p, q)
        (Named k, Named l)         -> k < l
        (Named _, Normal _ _)      -> True
        (Normal _ _, Named _)      -> False
        (Normal b st, Normal c su) -> before b c or (b == c and stores_before st su)
        _                          -> False

fn stores_before st su -> r : st~List (Value, Value), su~List (Value, Value), r~Bool
    match (st, su)
        ([], [])                     -> False
        ([], _)                      -> True
        (_, [])                      -> False
        ((j, x) :: sr, (k, y) :: ur) ->
            before j k or (j == k and (before x y or (x == y and stores_before sr ur)))

# A value of unbounded sort `s` that isn't one of `used`: an integer or an
# element above them all, a sequence longer than them all, a constant
# array whose constant is none of theirs.
fn fresh sig s used -> r : sig~Sig, s~Sort, used~List Value, r~Option Value
    match s
        Int      -> Some (Integer (1 + max_int used))
        Unin _ _ -> Some (Element (1 + max_element used))
        Seq e    ->
            match value_of sig e
                Some d -> Some (Sequence (repeat (1 + max_length used) d))
                None   -> None
        Arr _ w  ->
            match fresh sig w (bases used)
                Some b -> Some (ArrayElem s (Normal b []))
                None   -> None
        _        -> None

fn max_element vs -> r : vs~List Value, r~Nat
    match vs
        []                -> 0
        Element n :: rest -> if n > max_element rest then n else max_element rest
        _ :: rest         -> max_element rest

fn max_int vs -> r : vs~List Value, r~Int
    match vs
        []                -> 0
        Integer n :: rest -> if n > max_int rest then n else max_int rest
        _ :: rest         -> max_int rest

fn max_length vs -> r : vs~List Value, r~Nat
    match vs
        []                  -> 0
        Sequence xs :: rest -> if list.length xs > max_length rest then list.length xs else max_length rest
        _ :: rest           -> max_length rest

fn repeat n x -> r : n~Nat, x~Value, r~List Value
    if n == 0 then [] else x :: repeat (n - 1) x

fn bases vs -> r : vs~List Value, r~List Value
    match vs
        []                               -> []
        ArrayElem _ (Normal b _) :: rest -> b :: bases rest
        _ :: rest                        -> bases rest

# Whether `base` and `stores` are a normal form at index sort `i`.
fn canonical sig dom i base stores -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, base~Value,
                                          stores~List (Value, Value), r~Bool
    if stores == []
        True
    else
        match index_kind sig dom i
            Listed es -> sorted_stores stores and no_store_of base stores and all_listed (list.drop 1 es) stores
            Unbounded -> sorted_stores stores and no_store_of base stores
            Opaque    -> False

fn all_listed es st -> r : es~List Value, st~List (Value, Value), r~Bool
    match st
        []             -> True
        (j, _) :: rest -> list.contains es j and all_listed es rest

fn sorted_stores st -> r : st~List (Value, Value), r~Bool
    match st
        []                       -> True
        [_]                      -> True
        (j, _) :: (k, x) :: rest -> before j k and sorted_stores ((k, x) :: rest)

fn no_store_of base st -> r : base~Value, st~List (Value, Value), r~Bool
    match st
        []             -> True
        (_, x) :: rest -> x != base and no_store_of base rest

# What `stores` hold at `i`, the first store at `i` hiding later ones, or
# `base`.
fn read_stores stores base i -> r : stores~List (Value, Value), base~Value, i~Value, r~Value
    match stores
        []             -> base
        (j, x) :: rest -> if j == i then x else read_stores rest base i

# `(j, x)` put in `st`, which is sorted, in its place, replacing a store at
# `j`.
fn insert_store j x st -> r : j~Value, x~Value, st~List (Value, Value), r~List (Value, Value)
    match st
        []             -> [(j, x)]
        (k, y) :: rest ->
            if j == k then (j, x) :: rest else if before j k then (j, x) :: st else (k, y) :: insert_store j x rest

fn drop_base base st -> r : base~Value, st~List (Value, Value), r~List (Value, Value)
    match st
        []             -> []
        (j, x) :: rest -> if x == base then drop_base base rest else (j, x) :: drop_base base rest

# `stores` sorted by index, the first store at an index hiding later ones.
fn sort_stores stores -> r : stores~List (Value, Value), r~List (Value, Value)
    match stores
        []             -> []
        (j, x) :: rest -> insert_store j x (sort_stores rest)

# The normal form of `base` with `stores` (the first store at an index
# hiding later ones), for index sort `i`.
fn normalize sig dom i base stores -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, base~Value,
                                          stores~List (Value, Value), r~Option ArrayId
    match index_kind sig dom i
        Listed es ->
            match es
                first :: others ->
                    let at_first = read_stores stores base first
                    Some (Normal at_first (listed_stores others stores base at_first))
                []              -> None
        Unbounded -> Some (Normal base (drop_base base (sort_stores stores)))
        Opaque    -> if stores == [] then Some (Normal base []) else None

# The stores at `es` (in order) of `stores` over `base`, but those equal to
# `at_first`.
fn listed_stores es stores base at_first -> r : es~List Value, stores~List (Value, Value), base~Value, at_first~Value,
                                                r~List (Value, Value)
    match es
        []        -> []
        e :: rest ->
            let x = read_stores stores base e
            if x == at_first then listed_stores rest stores base at_first else (e, x) :: listed_stores rest stores base at_first

# The index sort of array sort `s`.
fn index_of s -> r : s~Sort, r~Option Sort
    match s
        Arr i _ -> Some i
        _       -> None

fn normal_const sig dom s v -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, v~Value, r~Option ArrayId
    match index_of s
        Some i -> if pure v then normalize sig dom i v [] else None
        None   -> None

fn normal_store sig dom s id j x -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, id~ArrayId, j~Value, x~Value,
                                        r~Option ArrayId
    match (index_of s, id)
        (Some i, Normal b st) -> if pure j and pure x then normalize sig dom i b ((j, x) :: st) else None
        _                     -> None

fn normal_select id i -> r : id~ArrayId, i~Value, r~Option Value
    match id
        Normal b st -> if pure i then Some (read_stores st b i) else None
        _           -> None

# `a` plus `b` at every index, for arrays of `Int`s.
fn normal_sum sig dom s a b -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~ArrayId, b~ArrayId,
                                   r~Option ArrayId
    match (index_of s, a, b)
        (Some i, Normal (Integer x) sa, Normal (Integer y) sb) ->
            match sums_at sa sb (Integer x) (Integer y) (list.keys sa ++ list.keys sb)
                Some st -> normalize sig dom i (Integer (x + y)) st
                None    -> None
        _                                                      -> None

fn sums_at sa sb ba bb is -> r : sa~List (Value, Value), sb~List (Value, Value), ba~Value, bb~Value, is~List Value,
                                 r~Option (List (Value, Value))
    match is
        []        -> Some []
        j :: rest ->
            match (read_stores sa ba j, read_stores sb bb j, sums_at sa sb ba bb rest)
                (Integer p, Integer q, Some st) -> Some ((j, Integer (p + q)) :: st)
                _                               -> None

# An index where normal forms `a` and `b` of array sort `s` differ, if
# they are different: where their bases differ, the first listed element,
# an index stored in neither, or any index; else the first stored index
# where they differ.
fn normal_differ sig dom s a b -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~ArrayId, b~ArrayId, r~Value
    match (index_of s, a, b)
        (Some i, Normal ba sa, Normal bb sb) ->
            if ba != bb
                match index_kind sig dom i
                    Listed (e :: _) -> e
                    Unbounded       -> or_any (fresh sig i (list.keys sa ++ list.keys sb))
                    _               -> or_any (value_of sig i)
            else
                first_difference sa sb ba (list.keys sa ++ list.keys sb)
        _                                    -> Truth False

fn or_any r -> v : r~Option Value, v~Value
    match r
        Some x -> x
        None   -> Truth False

fn first_difference sa sb base is -> r : sa~List (Value, Value), sb~List (Value, Value), base~Value, is~List Value,
                                         r~Value
    match is
        []        -> Truth False
        j :: rest -> if read_stores sa base j != read_stores sb base j then j else first_difference sa sb base rest

# `m` with its arrays given their meaning as functions: constant arrays,
# stores and `map +` make normal forms, a normal form is read by its
# stores, and a `Named` array is read as `m` reads it. A `lambda` is not
# given. This is the model `refutes` evaluates in.
export fn normal_arrays sig m -> r : sig~Sig, m~Model, r~Model
    let select = \s id i ->
        match id
            Named _ -> m.select s id i
            _       -> normal_select id i
    let const = \s v -> normal_const sig m.domain s v
    let store = \s id j x -> normal_store sig m.domain s id j x
    let sum = \s a b -> normal_sum sig m.domain s a b
    let lambda = \_ _ _ _ _ -> None
    let differ = \s a b -> normal_differ sig m.domain s a b
    Model m.funs select const store sum lambda m.array_domain differ m.div_zero m.mod_zero m.nth_out m.wrong_sel m.domain m.fuel

# The normal form Z3's `((as const s) v)` names: for the readers of Z3's
# output.
export fn const_array sig dom s v -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, v~Value, r~Option Value
    match normal_const sig dom s v
        Some id -> Some (ArrayElem s id)
        None    -> None

# The normal form Z3's `(store a j x)` names, for `a` a normal form.
export fn store_array sig dom s a j x -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~Value, j~Value, x~Value,
                                             r~Option Value
    match a
        ArrayElem _ id ->
            match normal_store sig dom s id j x
                Some id2 -> Some (ArrayElem s id2)
                None     -> None
        _              -> None

# ── Equality ─────────────────────────────────────────────────────────────────

# Whether `a` and `b`, values of one sort, are equal. In the meaning, two
# values are equal exactly when they are equal as data: arrays are the same
# element. In `refutes`, a `Named` array is one Z3 printed without a normal
# form, and a `Closure` a `lambda`: either may be the same function as
# another array, so two different values where one holds such an array are
# not compared.
fn equal mode a b -> r : mode~Mode, a~Value, b~Value, r~Result Bool Unknown
    match mode
        AsGiven   -> Ok (a == b)
        Unfolding ->
            if a == b and settled a then Ok True else if pure a and pure b then Ok False else Err ArraysCompared

# Whether `v` holds no `Unknown` (in a `lambda`'s captured variables):
# then two values that are the same data are the same value. Two closures
# that each captured an unknown are not known to be the same function, even
# when the reasons are the same.
fn settled v -> r : v~Value, r~Bool
    match v
        Sequence xs                     -> all_settled xs
        Constructed _ fs                -> all_settled fs
        ArrayElem _ (Normal b st)       -> settled b and stores_settled st
        ArrayElem _ (Closure env _ _ _) -> env_settled env
        _                               -> True

fn all_settled vs -> r : vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> settled v and all_settled rest

fn stores_settled st -> r : st~List (Value, Value), r~Bool
    match st
        []             -> True
        (j, x) :: rest -> settled j and settled x and stores_settled rest

fn env_settled rs -> r : rs~List (Result Value Unknown), r~Bool
    match rs
        []           -> True
        Ok v :: rest -> settled v and env_settled rest
        Err _ :: _   -> False

# Kleene's `and` of two answers.
fn both p q -> r : p~Result Bool Unknown, q~Result Bool Unknown, r~Result Bool Unknown
    match (p, q)
        (Ok False, _)      -> Ok False
        (_, Ok False)      -> Ok False
        (Ok True, Ok True) -> Ok True
        (Err e, _)         -> Err e
        (_, Err e)         -> Err e

# ── Evaluation ───────────────────────────────────────────────────────────────

# How definitions are evaluated: `AsGiven`, by the model; `Unfolding`, each
# one marked terminating as its own body.
export enum Mode
    AsGiven
    Unfolding

# What evaluation at one level uses: `value`, evaluation one level down (a
# definition's body, or a `lambda`'s, in `Unfolding`).
record Lower
    value~(List (Result Value Unknown) -> List Sort -> Term -> Result Value Unknown)

# Evaluation `fuel` levels deep at most.
fn level mode c m fuel -> low : mode~Mode, c~Context, m~Model, fuel~Nat, low~Lower
    if fuel == 0
        Lower (\_ _ _ -> Err OutOfFuel)
    else
        Lower (\env senv t -> value (level mode c m (fuel - 1)) mode c m env senv t)

# The value of `t`, where `env` gives the values of its variables (`Var 0`
# first) and `senv` their sorts.
fn value low mode c m env senv t -> r : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                        senv~List Sort, t~Term, r~Result Value Unknown
    match t
        Var i          ->
            match list.head (list.drop i env)
                Some v -> v
                None   -> Err IllSorted
        App h args     -> apply low mode c m env senv t h args
        Let binds body ->
            # A `let` binds all its names at once, each in the outer
            # environment; it must bind at least one (`term.sort_of`).
            if binds == []
                Err IllSorted
            else
                match term.sorts_of (term.signature c) senv (bound_terms binds)
                    Ok ss -> value low mode c m (list.reverse (bound low mode c m env senv binds) ++ env) (list.reverse ss ++ senv) body
                    Err _ -> Err IllSorted
        # In the meaning, the array the model names for this `lambda` and
        # the values of the variables around it; in `refutes`, the closure.
        Lam _ x body   ->
            let s = try sort_here c senv t
            match mode
                AsGiven   ->
                    let vs = try all_known env
                    given_array c m s LambdaNotGiven (m.lambda s vs senv x body)
                Unfolding -> Ok (ArrayElem s (Closure env senv x body))

fn bound_terms binds -> ts : binds~List (Name, Term), ts~List Term
    match binds
        []             -> []
        (_, t) :: rest -> t :: bound_terms rest

fn bound low mode c m env senv binds -> rs : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                             senv~List Sort, binds~List (Name, Term), rs~List (Result Value Unknown)
    match binds
        []             -> []
        (_, t) :: rest -> value low mode c m env senv t :: bound low mode c m env senv rest

fn values low mode c m env senv ts -> rs : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                           senv~List Sort, ts~List Term, rs~List (Result Value Unknown)
    match ts
        []        -> []
        t :: rest -> value low mode c m env senv t :: values low mode c m env senv rest

# Every result, if each is a value.
fn all_known rs -> r : rs~List (Result Value Unknown), r~Result (List Value) Unknown
    match rs
        []           -> Ok []
        Ok v :: rest ->
            let vs = try all_known rest
            Ok (v :: vs)
        Err e :: _   -> Err e

# The sort of `t` (whose head is applied here).
fn sort_here c senv t -> r : c~Context, senv~List Sort, t~Term, r~Result Sort Unknown
    match term.sort_of (term.signature c) senv t
        Ok s  -> Ok s
        Err _ -> Err IllSorted

# `h` applied to `args`; `t` is the whole application.
fn apply low mode c m env senv t h args -> r : low~Lower, mode~Mode, c~Context, m~Model,
                                               env~List (Result Value Unknown), senv~List Sort, t~Term, h~Head,
                                               args~List Term, r~Result Value Unknown
    match h
        Prim op    -> prim low mode c m env senv t op args
        Num n      -> Ok (Integer n)
        Boolean b  -> Ok (Truth b)
        EmptySeq _ -> Ok (Sequence [])
        ConstArr s ->
            match values low mode c m env senv args
                [v] ->
                    let x = try v
                    given_array c m s (NotGiven h) (m.const s x)
                _   -> Err IllSorted
        # The datatype `d` is not needed: a well-sorted term applies a
        # tester or selector only to values of its own datatype.
        Con _ k _  ->
            let vs = try all_known (values low mode c m env senv args)
            Ok (Constructed k vs)
        Is _ k     ->
            match values low mode c m env senv args
                [v] ->
                    match v
                        Ok (Constructed l _) -> Ok (Truth (k == l))
                        Ok _                 -> Err IllSorted
                        Err e                -> Err e
                _   -> Err IllSorted
        Sel d k j  ->
            match (args, values low mode c m env senv args)
                ([a], [v]) ->
                    match v
                        Ok (Constructed l fs) ->
                            if k == l
                                match list.head (list.drop j fs)
                                    Some x -> Ok x
                                    None   -> Err IllSorted
                            else
                                let s = try sort_here c senv a
                                let fs_sort = try sort_here c senv t
                                match s
                                    Data _ sargs -> given c m fs_sort h (m.wrong_sel d k j sargs (Constructed l fs))
                                    _            -> Err IllSorted
                        Ok _                  -> Err IllSorted
                        Err e                 -> Err e
                _          -> Err IllSorted
        Fun f      -> call low mode c m senv t f (values low mode c m env senv args)

# The definition of the `f`-th function, if it has one.
fn definition ds f -> r : ds~List (Nat, Def), f~Nat, r~Option Def
    match ds
        []             -> None
        (g, d) :: rest -> if g == f then Some d else definition rest f

# The `f`-th function at arguments `rs`.
fn call low mode c m senv t f rs -> r : low~Lower, mode~Mode, c~Context, m~Model, senv~List Sort, t~Term, f~Nat,
                                        rs~List (Result Value Unknown), r~Result Value Unknown
    match (mode, definition (term.defs c) f)
        (Unfolding, Some d) ->
            if d.terminates then low.value (list.reverse rs) (term.binder_env d.params) d.body else Err NotTerminating
        _                   ->
            let vs = try all_known rs
            let s = try sort_here c senv t
            given c m s (Fun f) (m.funs f vs)

fn as_bool r -> b : r~Result Value Unknown, b~Result Bool Unknown
    match r
        Ok (Truth x) -> Ok x
        Ok _         -> Err IllSorted
        Err e        -> Err e

fn as_int r -> n : r~Result Value Unknown, n~Result Int Unknown
    match r
        Ok (Integer x) -> Ok x
        Ok _           -> Err IllSorted
        Err e          -> Err e

fn truth r -> v : r~Result Bool Unknown, v~Result Value Unknown
    match r
        Ok b  -> Ok (Truth b)
        Err e -> Err e

# Kleene's `and` of `ts`, left to right, stopping at a definite `False`.
fn conj low mode c m env senv ts -> r : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                        senv~List Sort, ts~List Term, r~Result Bool Unknown
    match ts
        []        -> Ok True
        t :: rest ->
            match as_bool (value low mode c m env senv t)
                Ok False -> Ok False
                first    -> both first (conj low mode c m env senv rest)

# Kleene's `or` of `ts`, left to right, stopping at a definite `True`.
fn disj low mode c m env senv ts -> r : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                        senv~List Sort, ts~List Term, r~Result Bool Unknown
    match ts
        []        -> Ok False
        t :: rest ->
            match as_bool (value low mode c m env senv t)
                Ok True -> Ok True
                first   -> either first (disj low mode c m env senv rest)

# Kleene's `or` of two answers.
fn either p q -> r : p~Result Bool Unknown, q~Result Bool Unknown, r~Result Bool Unknown
    match (p, q)
        (Ok True, _)         -> Ok True
        (_, Ok True)         -> Ok True
        (Ok False, Ok False) -> Ok False
        (Err e, _)           -> Err e
        (_, Err e)           -> Err e

fn negate r -> s : r~Result Bool Unknown, s~Result Bool Unknown
    match r
        Ok b  -> Ok (not b)
        Err e -> Err e

# Integers `x` and `y`, both known, combined by `f`.
fn ints rx ry f -> r : rx~Result Value Unknown, ry~Result Value Unknown, f~(Int -> Int -> Result Value Unknown),
                       r~Result Value Unknown
    let x = try as_int rx
    let y = try as_int ry
    f x y

fn items r -> xs : r~Result Value Unknown, xs~Result (List Value) Unknown
    match r
        Ok (Sequence ys) -> Ok ys
        Ok _             -> Err IllSorted
        Err e            -> Err e

fn concat_all rs -> r : rs~List (Result Value Unknown), r~Result (List Value) Unknown
    match rs
        []        -> Ok []
        x :: rest ->
            let xs = try items x
            let ys = try concat_all rest
            Ok (xs ++ ys)

# The built-in operation `op` applied to `args`; `t` is the whole term.
fn prim low mode c m env senv t op args -> r : low~Lower, mode~Mode, c~Context, m~Model,
                                               env~List (Result Value Unknown), senv~List Sort, t~Term, op~Op,
                                               args~List Term, r~Result Value Unknown
    match (op, args)
        (Not, [a])              -> truth (negate (as_bool (value low mode c m env senv a)))
        (And, _)                -> truth (conj low mode c m env senv args)
        (Or, _)                 -> truth (disj low mode c m env senv args)
        (Implies, [a, b])       ->
            match as_bool (value low mode c m env senv a)
                Ok False -> Ok (Truth True)
                first    -> truth (either (negate first) (as_bool (value low mode c m env senv b)))
        (Ite, [p, a, b])        ->
            match as_bool (value low mode c m env senv p)
                Ok True  -> value low mode c m env senv a
                Ok False -> value low mode c m env senv b
                Err e    -> Err e
        (Eq, [a, b])            ->
            let x = try value low mode c m env senv a
            let y = try value low mode c m env senv b
            truth (equal mode x y)
        (Add, [a, b])           -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Integer (x + y)))
        (Sub, [a, b])           -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Integer (x - y)))
        (Mul, [a, b])           -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Integer (x * y)))
        (Neg, [a])              ->
            let x = try as_int (value low mode c m env senv a)
            Ok (Integer (0 - x))
        # Euclidean, as SMT-LIB's `Ints` theory defines `div` and `mod` (the
        # remainder is never negative), and as Checkers' `/` and `%` are. By
        # zero, they are what the model says.
        (Div, [a, b])           ->
            ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> if y != 0 then Ok (Integer (x / y)) else int_given (m.div_zero x) (Prim Div))
        (Mod, [a, b])           ->
            ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> if y != 0 then Ok (Integer (x % y)) else int_given (m.mod_zero x) (Prim Mod))
        (Lt, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x < y)))
        (Le, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x <= y)))
        (Gt, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x > y)))
        (Ge, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x >= y)))
        (Select, [a, i])        ->
            let x = try value low mode c m env senv a
            let j = try value low mode c m env senv i
            let s = try sort_here c senv a
            let w = try sort_here c senv t
            match x
                ArrayElem _ (Closure cenv csenv x_sort body) -> low.value (Ok j :: cenv) (x_sort :: csenv) body
                ArrayElem _ id                               -> given c m w (Prim Select) (m.select s id j)
                _                                            -> Err IllSorted
        (Store, [a, i, v])      ->
            let x = try value low mode c m env senv a
            let j = try value low mode c m env senv i
            let y = try value low mode c m env senv v
            let s = try sort_here c senv t
            match x
                ArrayElem _ id -> given_array c m s (NotGiven (Prim Store)) (m.store s id j y)
                _              -> Err IllSorted
        (MapAdd, [a, b])        ->
            let x = try value low mode c m env senv a
            let y = try value low mode c m env senv b
            let s = try sort_here c senv t
            match (x, y)
                (ArrayElem _ p, ArrayElem _ q) -> given_array c m s (NotGiven (Prim MapAdd)) (m.sum s p q)
                _                              -> Err IllSorted
        (SeqLen, [a])           ->
            let xs = try items (value low mode c m env senv a)
            Ok (Integer (list.length xs))
        # Inside the sequence, its element; outside, what the model says
        # (Z3 leaves `seq.nth` out of range unspecified).
        (SeqNth, [a, i])        ->
            let xs = try items (value low mode c m env senv a)
            let n = try as_int (value low mode c m env senv i)
            if 0 <= n and n < list.length xs
                match list.head (list.drop n xs)
                    Some x -> Ok x
                    None   -> Err IllSorted
            else
                let s = try sort_here c senv t
                given c m s (Prim SeqNth) (m.nth_out s xs n)
        (SeqUnit, [a])          ->
            let x = try value low mode c m env senv a
            Ok (Sequence [x])
        (SeqConcat, _)          ->
            let xs = try concat_all (values low mode c m env senv args)
            Ok (Sequence xs)
        # `n` elements from `i`, as many as there are; empty unless
        # `0 <= i < len` and `0 < n` (SMT-LIB's `str.substr`, and Z3's
        # `seq.extract`).
        (SeqExtract, [a, i, n]) ->
            let xs = try items (value low mode c m env senv a)
            let from = try as_int (value low mode c m env senv i)
            let count = try as_int (value low mode c m env senv n)
            if 0 <= from and from < list.length xs and 0 < count
                Ok (Sequence (list.take count (list.drop from xs)))
            else
                Ok (Sequence [])
        _                       -> Err IllSorted

fn int_given got h -> r : got~Option Int, h~Head, r~Result Value Unknown
    match got
        Some n -> Ok (Integer n)
        None   -> Err (NotGiven h)

# ── The meaning ──────────────────────────────────────────────────────────────

# The value of `t` in `m`, if `t` is a term of `c` without free variables
# (else `IllSorted`).
export fn eval c m t -> r : c~Context, m~Model, t~Term, r~Result Value Unknown
    if closed c t
        value (level AsGiven c m m.fuel) AsGiven c m [] [] t
    else
        Err IllSorted

# Whether `t` is a term of `c` without free variables: it has a sort there.
fn closed c t -> r : c~Context, t~Term, r~Bool
    match term.sort_of (term.signature c) [] t
        Ok _  -> True
        Err _ -> False

# Whether `t` is true in `m`.
export fn holds c m t -> r : c~Context, m~Model, t~Term, r~Bool
    eval c m t == Ok (Truth True)

# Whether `t` is false in `m`.
export fn fails c m t -> r : c~Context, m~Model, t~Term, r~Bool
    eval c m t == Ok (Truth False)

# Whether each of `ts` is true in `m`.
export fn holds_all c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> holds c m t and holds_all c m rest

# Whether each of `vs` is a value of the sort in the same place of `ss`.
export fn values_of_sorts c m ss vs -> r : c~Context, m~Model, ss~List Sort, vs~List Value, r~Bool
    fields_of_sort c m ss vs

# Whether axiom `a` holds at the values `vs` of its variables, in order.
# Values that aren't of the variables' sorts in `m` are not among the ones
# `a` speaks of, so it holds at them: as a hypothesis ("`a` holds at all
# values") this asks nothing of them, and as a conclusion it says nothing
# about them. An axiom that isn't one of `c` (`term.axiom_ok`) holds nowhere.
export fn holds_at c m a vs -> r : c~Context, m~Model, a~Axiom, vs~List Value, r~Bool
    if not (term.axiom_ok c a)
        False
    else if values_of_sorts c m (term.var_sorts a.vars) vs
        value (level AsGiven c m m.fuel) AsGiven c m (list.reverse (list.map (\v -> Ok v) vs)) (term.binder_env a.vars) a.body
            == Ok (Truth True)
    else
        True

# The equation of definition `d`, the `n`-th function: for all values of
# its parameters, `(= (f x1 … xk) body)`. In the meaning a definition is
# this fact, so a model satisfies `d` when `holds_at` is true for it at all
# values.
export fn definition_axiom n d -> a : n~Nat, d~Def, a~Axiom
    let k = list.length d.params
    Axiom d.params (App (Prim Eq) [App (Fun n) (params_from k), d.body]) []

# `Var (k - 1)`, …, `Var 0`: the parameters of a binder list of `k`, in
# order (the last one bound is `Var 0`).
fn params_from k -> ts : k~Nat, ts~List Term
    if k == 0 then [] else Var (k - 1) :: params_from (k - 1)

# The value of `t` with each definition marked terminating run as its own
# body, if `t` is a term of `c` without free variables (else `IllSorted`).
export fn eval_unfolding c m t -> r : c~Context, m~Model, t~Term, r~Result Value Unknown
    if closed c t
        value (level Unfolding c m m.fuel) Unfolding c m [] [] t
    else
        Err IllSorted

# Whether every definition of `ds` is marked terminating.
fn all_marked ds -> r : ds~List (Nat, Def), r~Bool
    match ds
        []             -> True
        (_, d) :: rest -> d.terminates and all_marked rest

# Whether `m` is a counterexample to `goal` in `c`: `goal` is a fact of `c`,
# `c` has no axioms and every definition is marked terminating, and each
# fact holds and the goal fails with each definition run as its own body,
# in `normal_arrays m`. Then the interpretation that model describes, with
# each definition its unique solution, satisfies every assertion of `c` and
# `not goal`.
#
# For arrays this rests on `normal_arrays`: its normal forms are the same
# element exactly when they are the same function, and an answer that
# compares an array Z3 printed without one is `ArraysCompared`, so no
# definite answer depends on how those compare.
#
# For definitions this rests entirely on the marks (`Def.terminates`): a
# mark promises that the definition's body terminates at every argument of
# its sorts, in every interpretation of the declared functions, so that the
# definition has exactly one solution. A wrong mark makes `refutes` wrong
# (`g x = g x + 1` marked and never called is "refuted", though the context
# has no model). The caller owes the marks: `ckc` (how it says so is #299).
export fn refutes c goal m -> r : c~Context, goal~Term, m~Model, r~Bool
    let n = normal_arrays (term.signature c) m
    term.fact_ok c goal and term.axioms c == [] and all_marked (term.defs c) and facts_hold_unfolding c n (term.facts c)
        and eval_unfolding c n goal == Ok (Truth False)

fn facts_hold_unfolding c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> eval_unfolding c m t == Ok (Truth True) and facts_hold_unfolding c m rest

# ── What makes them SMT-LIB's arrays: `arrays_ok` ────────────────────────────
# Each predicate below, held at all values of its arguments, is one of the
# conditions that make a model's arrays SMT-LIB's: `ArraysEx` (read over
# write, constant arrays), `map +` pointwise, a `lambda` read as its body,
# and extensionality. `arrays_ok` is all of `const_law`, `store_law`,
# `sum_law`, `lambda_law` and `ext_law` at all values; `arrays_total` is
# all of the `gives_` ones. They can't be computed, since each quantifies
# over every value: a theorem takes each as a named `forall` hypothesis
# (SPEC §9.9), such as
#
#     store: forall s id j x i : s~Sort, id~ArrayId, j~Value, x~Value, i~Value, model.store_law c m s id j x i
#
# Nothing in `eval` relies on them; only with them is a `Model` an SMT-LIB
# structure. Each says nothing where an argument isn't of its sort.

# The model answers `select` at elements and indices of their sorts, with a
# value of the element sort.
export fn gives_select c m s id i -> r : c~Context, m~Model, s~Sort, id~ArrayId, i~Value, r~Bool
    match s
        Arr ix w ->
            if of_sort c m s (ArrayElem s id) and of_sort c m ix i
                match m.select s id i
                    Some v -> of_sort c m w v
                    None   -> False
            else
                True
        _        -> True

# The model names the constant array of `v`.
export fn gives_const c m s v -> r : c~Context, m~Model, s~Sort, v~Value, r~Bool
    match s
        Arr _ w -> if of_sort c m w v then names_one c m s (m.const s v) else True
        _       -> True

# The model names the store of `x` at `j` in `id`.
export fn gives_store c m s id j x -> r : c~Context, m~Model, s~Sort, id~ArrayId, j~Value, x~Value, r~Bool
    match s
        Arr ix w ->
            if of_sort c m s (ArrayElem s id) and of_sort c m ix j and of_sort c m w x
                names_one c m s (m.store s id j x)
            else
                True
        _        -> True

# The model names the sum of `a` and `b`, arrays of `Int`s.
export fn gives_sum c m s a b -> r : c~Context, m~Model, s~Sort, a~ArrayId, b~ArrayId, r~Bool
    match s
        Arr _ Int ->
            if of_sort c m s (ArrayElem s a) and of_sort c m s (ArrayElem s b) then names_one c m s (m.sum s a b) else True
        _         -> True

# The model names the array of every `lambda` of sort `s` whose variables
# around it have values `env` of sorts `senv`.
export fn gives_lambda c m s env senv x body -> r : c~Context, m~Model, s~Sort, env~List Value, senv~List Sort, x~Sort,
                                                    body~Term, r~Bool
    if term.sort_of (term.signature c) senv (Lam b"x" x body) == Ok s and values_of_sorts c m (list.reverse senv) (list.reverse env)
        names_one c m s (m.lambda s env senv x body)
    else
        True

fn names_one c m s got -> r : c~Context, m~Model, s~Sort, got~Option ArrayId, r~Bool
    match got
        Some id -> of_sort c m s (ArrayElem s id)
        None    -> False

# Whether `j` and `i` are indices and `x` a value of array sort `s`.
fn sorted_at c m s j i x -> r : c~Context, m~Model, s~Sort, j~Value, i~Value, x~Value, r~Bool
    match s
        Arr ix w -> of_sort c m ix j and of_sort c m ix i and of_sort c m w x
        _        -> False

# A constant array is `v` at every index `i`.
export fn const_law c m s v i -> r : c~Context, m~Model, s~Sort, v~Value, i~Value, r~Bool
    if sorted_at c m s i i v
        match m.const s v
            Some id -> m.select s id i == Some v
            None    -> True
    else
        True

# Read over write: a store of `x` at `j` is `x` at `j`, and elsewhere what
# it was.
export fn store_law c m s id j x i -> r : c~Context, m~Model, s~Sort, id~ArrayId, j~Value, x~Value, i~Value, r~Bool
    if sorted_at c m s j i x and of_sort c m s (ArrayElem s id)
        match m.store s id j x
            Some id2 -> m.select s id2 i == (if i == j then Some x else m.select s id i)
            None     -> True
    else
        True

# `map +` adds the two arrays at every index `i`.
export fn sum_law c m s a b i -> r : c~Context, m~Model, s~Sort, a~ArrayId, b~ArrayId, i~Value, r~Bool
    if sorted_at c m s i i (Integer 0) and of_sort c m s (ArrayElem s a) and of_sort c m s (ArrayElem s b)
        match m.sum s a b
            Some id ->
                match (m.select s a i, m.select s b i)
                    (Some (Integer p), Some (Integer q)) -> m.select s id i == Some (Integer (p + q))
                    _                                    -> False
            None    -> True
    else
        True

# A `lambda` is, at every index `i`, its body with the variable at `i`,
# wherever the body has a value there.
export fn lambda_law c m s env senv x body i -> r : c~Context, m~Model, s~Sort, env~List Value, senv~List Sort, x~Sort,
                                                    body~Term, i~Value, r~Bool
    if of_sort c m x i
        match m.lambda s env senv x body
            Some id ->
                let at = Ok i :: list.map (\v -> Ok v) env
                match value (level AsGiven c m m.fuel) AsGiven c m at (x :: senv) body
                    Ok v  -> m.select s id i == Some v
                    Err _ -> True
            None    -> True
    else
        True

# Extensionality: two different elements of `s` differ at the index
# `differ` gives.
export fn ext_law c m s a b -> r : c~Context, m~Model, s~Sort, a~ArrayId, b~ArrayId, r~Bool
    match s
        Arr ix _ ->
            if a != b and of_sort c m s (ArrayElem s a) and of_sort c m s (ArrayElem s b)
                let i = m.differ s a b
                of_sort c m ix i and m.select s a i != m.select s b i
            else
                True
        _        -> True
