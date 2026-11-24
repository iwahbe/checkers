# model.ck — what a term means in a model: `eval`, `holds`, `fails`.
#
# This module is the definition every answer of the solver is checked
# against (#72, design 1). It is written to be read, not to be fast: each
# operation says what it computes, and where SMT-LIB leaves a result
# unspecified, the model says what it is.
#
# **Three answers.** Evaluating a term gives its value, or `Unknown` with a
# reason: the model doesn't say (a partial model, such as the values Z3
# printed), evaluation ran out of fuel, two arrays were compared that this
# module can't compare, or the model gave a value of the wrong sort.
# `holds c m t` is true only when `t` evaluates to true, and `fails c m t`
# only when it evaluates to false; when neither, nothing is claimed. A
# definite answer is always the term's value in the interpretation the
# model describes, so a counterexample built on `holds` and `fails` is real.
#
# **Connectives are Kleene's.** `and` is false as soon as one argument is
# false, whatever the others are, and true only if all are true; `or`
# dually; `=>` is `(not a) or b`. This is exact: every term has a value in
# every interpretation, so a conjunction with a false argument is false
# whatever the unknown arguments' values are. `ite` evaluates its condition,
# then only the branch it chooses.
#
# **Fuel.** Applying a `lambda` and unfolding a definition evaluate a term
# that isn't part of the one being evaluated, so each goes one level down,
# and `Model.fuel` bounds how many levels there are; past it the answer is
# `OutOfFuel`. Comparing two constant arrays with stores compares the values
# at their indices one level down in the same way (so with `fuel = 0`, such
# arrays compare `OutOfFuel`). Comparing sequences and data goes by their
# structure and uses no fuel.
#
# **Terms of the context only.** `eval`, `holds_at` and `refutes` evaluate a
# term only if it is a term of the context (`term.fact_ok`, `term.axiom_ok`);
# anything else is `IllSorted`.
#
# **Two modes.** `eval`, `holds`, `fails`, `holds_all` and `holds_at` are the
# meaning: every function, defined ones included, is what `Model.funs` says,
# and a definition's equation is a fact like any other (SMT-LIB defines
# `define-fun-rec` as a declared function and its universally quantified
# equation). `refutes`, which `Answer.Invalid` uses, evaluates instead with
# each definition marked terminating (`Def.terminates`) run as its own body
# (design 3): its equation then holds by construction wherever evaluation
# finishes, because a terminating definition has exactly one solution.
# `refutes` requires every definition of the context to be marked: one that
# isn't may have no solution at all (`g x = g x + 1`), and then no model
# satisfies the context, whether or not an assertion calls it (SMT-LIB 2.6,
# §4.2.3, note 4). Z3 5.3.3 answers `sat` to such a context; this module
# does not follow it there. Unfolding a definition not marked terminating is
# `NotTerminating`. In the meaning, a model satisfies definition `d` when it
# satisfies `definition_axiom n d` at all values (`holds_at`).
#
# **Quantified axioms.** `holds_at c m a vs` evaluates the body of axiom `a`
# at the values `vs`. A `forall` over an infinite sort can't be evaluated, so
# `refutes` is false for a context with any axiom, patterned or not (an
# `Axiom` with `patterns = []` is a fact like the others, #82): a model is
# never shown to satisfy one, so a query with one is never `Invalid`.
#
# **What a model can't represent here** (for #85, model limits): equality of
# two arrays is decided only when both are a constant array with stores and
# the answer follows from the stored indices (see `equal`); otherwise it is
# `ArraysCompared`. Arrays given by the model (`ModelArray s k`, one family
# for each array sort `s`) are functions of values; a model function, selector or `seq.nth` applied to a value that
# holds an array is `ArraysCompared` too, since two different values may
# then be the same array, and a function must give them the same result.

module model

import std.list
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, FunDecl, Def, Axiom, Context)
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
# - Arrays, which are total functions from index values to values:
#   `ConstArray i v` maps every index of sort `i` to `v`; `StoreArray a j v`
#   is `a` with index `j` mapped to `v`; `LambdaArray env senv s body` is a
#   `lambda` over a variable of sort `s`, with the values and sorts of the
#   variables bound around it; `SumArray a b` is `(_ map (+ (Int Int) Int))`
#   of `a` and `b`; `ModelArray s k` is the model's `k`-th array of sort `s`
#   (`Model.arrays`).
export enum Value
    Truth b                     : b~Bool
    Integer n                   : n~Int
    Sequence xs                 : xs~List Value
    Constructed k fields        : k~Nat, fields~List Value
    Element n                   : n~Nat
    ConstArray i v              : i~Sort, v~Value
    StoreArray a j v            : a~Value, j~Value, v~Value
    LambdaArray env senv s body : env~List (Result Value Unknown), senv~List Sort, s~Sort, body~Term
    SumArray a b                : a~Value, b~Value
    ModelArray s k              : s~Sort, k~Nat

# Why a term has no value here.
export enum Unknown
    # The model doesn't say: what `h` gives at these arguments (`Fun f` for
    # a function; `Prim Div` or `Prim Mod` for a division by zero; `Prim
    # SeqNth` for an index out of range; `Sel d k j` for a selector applied
    # to another constructor's value; `Prim Select` for a model's array).
    NotGiven h : h~Head
    # Evaluation needed more than `Model.fuel` levels.
    OutOfFuel
    # Two arrays compared, or an array given to something the model
    # defines, where this module can't tell which array it is.
    ArraysCompared
    # A call of a definition not marked terminating, in `refutes`.
    NotTerminating
    # The model gave a value that isn't of the sort needed.
    WrongSort
    # The term isn't a term of the context. Never for one that is.
    IllSorted

# The elements of an uninterpreted sort: `UpTo n` is `Element 0` to
# `Element n` (never empty, as SMT-LIB requires); `Countable` is every
# `Element n`. Countable domains are all first-order logic needs
# (Löwenheim–Skolem).
export enum Domain
    UpTo n : n~Nat
    Countable

# An interpretation of a context's symbols, and of what SMT-LIB leaves
# unspecified. Each function may answer `None`: then the model doesn't say,
# and a term that needs it is `NotGiven`. A complete model answers `Some`
# everywhere.
#
# - `funs f vs`: the `f`-th function at arguments `vs`; a constant at `[]`.
# - `arrays s k v`: the model's `k`-th array of sort `s` at index `v`.
# - `div_zero n`, `mod_zero n`: `(div n 0)` and `(mod n 0)`. SMT-LIB leaves
#   them unspecified; each is a function of `n`, and the two are unrelated.
# - `nth_out e xs i`: `(seq.nth xs i)` for `i` outside `xs`, where the
#   elements are of sort `e`: a function of `xs` and `i`.
# - `wrong_sel d k j args v`: selector `j` of constructor `k` of datatype
#   `d` (at sort arguments `args`) applied to `v`, built by another
#   constructor: a function of `v`.
# - `domain u args`: the elements of `Unin u args`.
# - `fuel`: how many levels evaluation may go down (see the module's
#   comment).
#
# What a model gives is checked against the sort needed (`of_sort`), so a
# model can't make a term take a value outside its sort.
export record Model
    funs~(Nat -> List Value -> Option Value)
    arrays~(Sort -> Nat -> Value -> Option Value)
    div_zero~(Int -> Option Int)
    mod_zero~(Int -> Option Int)
    nth_out~(Sort -> List Value -> Int -> Option Value)
    wrong_sel~(Nat -> Nat -> Nat -> List Sort -> Value -> Option Value)
    domain~(Nat -> List Sort -> Domain)
    fuel~Nat

# ── Sorts of values ──────────────────────────────────────────────────────────

fn in_domain d n -> r : d~Domain, n~Nat, r~Bool
    match d
        UpTo last -> n <= last
        Countable -> True

# Whether `v`, given by the model, is a value of sort `s`. Arrays given by
# a model are constant arrays with stores, or the model's own arrays.
export fn of_sort c m s v -> r : c~Context, m~Model, s~Sort, v~Value, r~Bool
    match (s, v)
        (Bool, Truth _)                 -> True
        (Int, Integer _)                -> True
        (Seq e, Sequence xs)            -> all_of_sort c m e xs
        (Arr i w, ConstArray j x)       -> i == j and of_sort c m w x
        (Arr i w, StoreArray a j x)     -> of_sort c m s a and of_sort c m i j and of_sort c m w x
        (Arr _ _, ModelArray t _)       -> t == s
        (Data d args, Constructed k fs) ->
            match term.ctor (term.signature c) d k
                Some k_ctor -> fields_of_sort c m (list.map (term.instantiate args) (term.field_sorts k_ctor.fields)) fs
                None        -> False
        (Unin u args, Element n)        -> in_domain (m.domain u args) n
        _                               -> False

fn all_of_sort c m s vs -> r : c~Context, m~Model, s~Sort, vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> of_sort c m s v and all_of_sort c m s rest

fn fields_of_sort c m ss vs -> r : c~Context, m~Model, ss~List Sort, vs~List Value, r~Bool
    match (ss, vs)
        ([], [])           -> True
        (s :: sr, v :: vr) -> of_sort c m s v and fields_of_sort c m sr vr
        _                  -> False

# What the model said, `got`, for a term of sort `s` that needs `h`.
fn given c m s h got -> r : c~Context, m~Model, s~Sort, h~Head, got~Option Value, r~Result Value Unknown
    match got
        None   -> Err (NotGiven h)
        Some v -> if of_sort c m s v then Ok v else Err WrongSort

# Whether `v` holds no array: two such values are the same value exactly
# when they are equal as data, so a model's function can be asked about it.
export fn plain v -> r : v~Value, r~Bool
    match v
        Truth _          -> True
        Integer _        -> True
        Element _        -> True
        Sequence xs      -> all_plain xs
        Constructed _ fs -> all_plain fs
        _                -> False

fn all_plain vs -> r : vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> plain v and all_plain rest

# ── Equality ─────────────────────────────────────────────────────────────────

# Whether `a` and `b`, values of one sort, are equal; `down` compares values
# one level down. Data are equal when built alike from equal parts. Arrays:
# the same value is the same array; two constant arrays with stores are
# compared at every stored index of either, and if they agree there, their
# constants decide: equal constants make equal arrays, and different ones
# different arrays when the index sort is infinite (`Int`, `Seq`), or
# `Bool` with both indices stored. Anything else is `ArraysCompared`.
fn equal_with down a b -> r : down~(Value -> Value -> Result Bool Unknown), a~Value, b~Value, r~Result Bool Unknown
    match (a, b)
        (Truth x, Truth y)                   -> Ok (x == y)
        (Integer x, Integer y)               -> Ok (x == y)
        (Element x, Element y)               -> Ok (x == y)
        (Sequence xs, Sequence ys)           ->
            if list.length xs != list.length ys then Ok False else equal_all down xs ys
        (Constructed k xs, Constructed l ys) ->
            if k != l then Ok False else if list.length xs != list.length ys then Err IllSorted else equal_all down xs ys
        (Truth _, _)                         -> Err IllSorted
        (Integer _, _)                       -> Err IllSorted
        (Element _, _)                       -> Err IllSorted
        (Sequence _, _)                      -> Err IllSorted
        (Constructed _ _, _)                 -> Err IllSorted
        _                                    -> if a == b and settled a then Ok True else equal_arrays down a b

# Element by element, with Kleene's `and`: a definite `False` wins. Lists
# of different lengths are not values of one sort.
fn equal_all down xs ys -> r : down~(Value -> Value -> Result Bool Unknown), xs~List Value, ys~List Value,
                               r~Result Bool Unknown
    match (xs, ys)
        ([], [])           -> Ok True
        (x :: xr, y :: yr) -> both (equal_with down x y) (equal_all down xr yr)
        _                  -> Err IllSorted

# Whether `v` holds no `Unknown` (in a `lambda`'s captured variables): then
# two values that are the same data are the same value. Two closures that
# each captured an unknown value are not known to be the same function, even
# when the reasons are the same.
fn settled v -> r : v~Value, r~Bool
    match v
        Sequence xs           -> all_settled xs
        Constructed _ fs      -> all_settled fs
        ConstArray _ x        -> settled x
        StoreArray a j x      -> settled a and settled j and settled x
        LambdaArray env _ _ _ -> env_settled env
        SumArray a b          -> settled a and settled b
        _                     -> True

fn all_settled vs -> r : vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> settled v and all_settled rest

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

# A constant array with stores: its index sort, its constant, and its
# stores, outermost first (an earlier one hides a later one at its index).
record Finite
    index~Sort
    base~Value
    stores~List (Value, Value)

fn finite a -> r : a~Value, r~Option Finite
    match a
        ConstArray i v   -> Some (Finite i v [])
        StoreArray b j v ->
            match finite b
                Some f -> Some (Finite f.index f.base ((j, v) :: f.stores))
                None   -> None
        _                -> None

# What a constant array with stores holds at `i`.
fn lookup down f i -> r : down~(Value -> Value -> Result Bool Unknown), f~Finite, i~Value, r~Result Value Unknown
    lookup_in down f.stores f.base i

fn lookup_in down stores base i -> r : down~(Value -> Value -> Result Bool Unknown), stores~List (Value, Value),
                                       base~Value, i~Value, r~Result Value Unknown
    match stores
        []             -> Ok base
        (j, v) :: rest ->
            match down i j
                Ok True  -> Ok v
                Ok False -> lookup_in down rest base i
                Err e    -> Err e

fn equal_arrays down a b -> r : down~(Value -> Value -> Result Bool Unknown), a~Value, b~Value, r~Result Bool Unknown
    match (finite a, finite b)
        (Some f, Some g) ->
            let indices = list.keys f.stores ++ list.keys g.stores
            match agree_at down f g indices
                Ok True ->
                    match down f.base g.base
                        Ok True  -> Ok True
                        Ok False -> different_bases down f.index indices
                        Err e    -> Err e
                other   -> other
        _                -> Err ArraysCompared

# Whether `f` and `g` agree at each of `is`.
fn agree_at down f g is -> r : down~(Value -> Value -> Result Bool Unknown), f~Finite, g~Finite, is~List Value,
                               r~Result Bool Unknown
    match is
        []        -> Ok True
        i :: rest ->
            let here =
                match (lookup down f i, lookup down g i)
                    (Ok x, Ok y) -> down x y
                    (Err e, _)   -> Err e
                    (_, Err e)   -> Err e
            both here (agree_at down f g rest)

# Two arrays that agree at the stored indices `is` and have different
# constants: different exactly when some index isn't stored.
fn different_bases down index is -> r : down~(Value -> Value -> Result Bool Unknown), index~Sort, is~List Value,
                                        r~Result Bool Unknown
    match index
        Int   -> Ok False
        Seq _ -> Ok False
        Bool  ->
            match (stored down is (Truth True), stored down is (Truth False))
                (Ok True, Ok True) -> Ok True
                (Ok _, Ok _)       -> Ok False
                (Err e, _)         -> Err e
                (_, Err e)         -> Err e
        _     -> Err ArraysCompared

# Whether `i` is one of `is`.
fn stored down is i -> r : down~(Value -> Value -> Result Bool Unknown), is~List Value, i~Value, r~Result Bool Unknown
    match is
        []        -> Ok False
        j :: rest ->
            match down i j
                Ok True  -> Ok True
                Ok False -> stored down rest i
                Err e    -> Err e

# Whether `a` and `b` are equal, comparing nested arrays `depth` levels down
# at most.
fn equal_to depth a b -> r : depth~Nat, a~Value, b~Value, r~Result Bool Unknown
    if depth == 0 then equal_with (\_ _ -> Err OutOfFuel) a b else equal_with (\x y -> equal_to (depth - 1) x y) a b

# ── Evaluation ───────────────────────────────────────────────────────────────

# How definitions are evaluated: `AsGiven`, by the model; `Unfolding`, each
# one marked terminating as its own body.
export enum Mode
    AsGiven
    Unfolding

# Evaluation one level down: a term in an environment, and equality.
record Lower
    value~(List (Result Value Unknown) -> List Sort -> Term -> Result Value Unknown)
    equal~(Value -> Value -> Result Bool Unknown)

# Evaluation `fuel` levels deep at most.
fn level mode c m fuel -> low : mode~Mode, c~Context, m~Model, fuel~Nat, low~Lower
    if fuel == 0
        Lower (\_ _ _ -> Err OutOfFuel) (\_ _ -> Err OutOfFuel)
    else
        Lower (\env senv t -> value (level mode c m (fuel - 1)) mode c m env senv t) (equal_to (fuel - 1))

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
            match if binds == [] then Err term.EmptyLet else term.sorts_of (term.signature c) senv (bound_terms binds)
                Ok ss -> value low mode c m (list.reverse (bound low mode c m env senv binds) ++ env) (list.reverse ss ++ senv) body
                Err _ -> Err IllSorted
        Lam _ s body   -> Ok (LambdaArray env senv s body)

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
            match (s, values low mode c m env senv args)
                (Arr i _, [v]) ->
                    let x = try v
                    Ok (ConstArray i x)
                _              -> Err IllSorted
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
                                    Data _ sargs ->
                                        if plain (Constructed l fs)
                                            given c m fs_sort h (m.wrong_sel d k j sargs (Constructed l fs))
                                        else
                                            Err ArraysCompared
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
            if all_plain vs then given c m s (Fun f) (m.funs f vs) else Err ArraysCompared

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
            truth (low.equal x y)
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
            let s = try sort_here c senv t
            select low c m s x j
        (Store, [a, i, v])      ->
            let x = try value low mode c m env senv a
            let j = try value low mode c m env senv i
            let w = try value low mode c m env senv v
            Ok (StoreArray x j w)
        (MapAdd, [a, b])        ->
            let x = try value low mode c m env senv a
            let y = try value low mode c m env senv b
            Ok (SumArray x y)
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
                if all_plain xs then given c m s (Prim SeqNth) (m.nth_out s xs n) else Err ArraysCompared
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

# Array `a` at index `i`, where the array's values are of sort `s`.
fn select low c m s a i -> r : low~Lower, c~Context, m~Model, s~Sort, a~Value, i~Value, r~Result Value Unknown
    match a
        ConstArray _ v                 -> Ok v
        StoreArray b j v               ->
            match low.equal i j
                Ok True  -> Ok v
                Ok False -> select low c m s b i
                Err e    -> Err e
        LambdaArray env senv sort body -> low.value (Ok i :: env) (sort :: senv) body
        SumArray x y                   ->
            ints (select low c m s x i) (select low c m s y i) (\p q -> Ok (Integer (p + q)))
        ModelArray t k                 ->
            if plain i then given c m s (Prim Select) (m.arrays t k i) else Err ArraysCompared
        _                              -> Err IllSorted

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
# `a` speaks of, so it holds at them. An axiom that isn't one of `c`
# (`term.axiom_ok`) holds nowhere.
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
# fact holds and the goal fails with each definition run as its own body.
# Then the interpretation `m` describes, with each definition its unique
# solution, satisfies every assertion of `c` and `not goal`.
export fn refutes c goal m -> r : c~Context, goal~Term, m~Model, r~Bool
    term.fact_ok c goal and term.axioms c == [] and all_marked (term.defs c) and facts_hold_unfolding c m (term.facts c)
        and eval_unfolding c m goal == Ok (Truth False)

fn facts_hold_unfolding c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> eval_unfolding c m t == Ok (Truth True) and facts_hold_unfolding c m rest
