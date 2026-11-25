# model_checks.ck — `check`s of `smt.model`'s meaning (`AsGiven`), which
# `main model` and `main models` don't run: `holds`, `fails`, `holds_all`,
# `holds_at` (with the model's arrays, one family per sort, and the domain of
# an uninterpreted sort), `definition_axiom`, a `lambda` named by the model,
# functions of arrays, fuel in `refutes`, normal forms, the `arrays_ok`
# laws at points, and terms that aren't the context's. Every `ckc check` of
# this file runs them.

module model_checks

import std.list
import smtlib (Query)
import term (Sort, Int, Bool, Arr, Unin, Context, Term, Var, App, Prim, Num, Boolean, And, Axiom, Def, ConstArr, Select)
import model (Value, Truth, Integer, Element, ArrayElem, ArrayId, Named, Normal, Model, Domain, UpTo, Countable)
import model (Unknown, NotGiven, LambdaNotGiven, OutOfFuel, ArraysCompared, NotTerminating, IllSorted)
import models

# The query `src` reads to, or the empty one.
fn query src -> q : src~Bytes, q~Option Query
    match smtlib.parse src
        Ok x  -> Some x
        Err _ -> None

fn context src -> c : src~Bytes, c~Context
    match query src
        Some q -> q.context
        None   -> term.empty

fn facts src -> ts : src~Bytes, ts~List Term
    term.facts (context src)

fn fact src k -> t : src~Bytes, k~Nat, t~Term
    match list.head (list.drop k (facts src))
        Some x -> x
        None   -> App (Boolean False) []

fn axiom src k -> a : src~Bytes, k~Nat, a~Axiom
    match list.head (list.drop k (term.axioms (context src)))
        Some x -> x
        None   -> Axiom [] (App (Boolean False) []) []

# A model: the functions `funs`, the arrays' `select`, the domains
# `domain`, with `fuel`; it says nothing else.
fn model_with funs select domain fuel -> m : funs~(Nat -> List Value -> Option Value),
                                             select~(Sort -> ArrayId -> Value -> Option Value),
                                             domain~(Nat -> List Sort -> Domain), fuel~Nat, m~Model
    let b = model.without_arrays funs (\_ -> None) (\_ -> None) (\_ _ _ -> None) (\_ _ _ _ _ -> None) domain fuel
    Model b.funs select b.const b.store b.sum b.lambda b.array_domain b.differ b.div_zero b.mod_zero b.nth_out b.wrong_sel b.domain b.fuel

fn constant v -> f : v~Value, f~(Nat -> List Value -> Option Value)
    \_ _ -> Some v

let NO_ARRAYS = \_ _ _ -> None

# ── holds, fails, holds_all ──────────────────────────────────────────────────

let X = b"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 5))(assert (not false))(check-sat)"

fn with_x v -> m : v~Value, m~Model
    model_with (constant v) NO_ARRAYS (\_ _ -> Countable) 10

let NOTHING = model_with (\_ _ -> None) NO_ARRAYS (\_ _ -> Countable) 10

check model.holds (context X) (with_x (Integer 1)) (fact X 0)
check model.fails (context X) (with_x (Integer 0)) (fact X 0)
check model.holds_all (context X) (with_x (Integer 1)) (facts X)
check not (model.holds_all (context X) (with_x (Integer 7)) (facts X))
# The model doesn't give `x`: neither true nor false.
check not (model.holds (context X) NOTHING (fact X 0)) and not (model.fails (context X) NOTHING (fact X 0))
# A value of the wrong sort from the model is not taken.
check not (model.holds (context X) (with_x (Truth True)) (fact X 0))

# ── Terms that aren't the context's ──────────────────────────────────────────

# `(and false 5)` isn't well-sorted, so it has no value, though `false`
# alone would decide it.
let ILL = App (Prim And) [App (Boolean False) [], App (Num 5) []]

check model.eval (context X) NOTHING ILL == Err IllSorted
check not (model.refutes (context X) ILL NOTHING)

# ── Definitions: the model's, or their own bodies ────────────────────────────

let F = b"(set-logic ALL)(define-fun-rec f ((n Int)) Int (+ n 1))(assert (= (f 1) 2))(assert (not false))(check-sat)"

fn marked_f -> c : c~Context
    match models.marked (context F)
        Ok c  -> c
        Err _ -> term.empty

# In the meaning, `f` is what the model says: here 7 everywhere.
check model.fails (context F) (with_x (Integer 7)) (fact F 0)
# Run as its own body, once marked terminating.
check model.eval_unfolding marked_f (with_x (Integer 7)) (fact F 0) == Ok (Truth True)
# Not marked: not run.
check model.eval_unfolding (context F) (with_x (Integer 7)) (fact F 0) == Err NotTerminating

fn def_f -> d : d~(Nat, Def)
    match term.defs (context F)
        d :: _ -> d
        []     -> (0, Def b"" [] Int (App (Num 0) []) False)

fn f_axiom -> a : a~Axiom
    let (n, d) = def_f
    model.definition_axiom n d

# A model whose `f` is `n + 1` satisfies the definition; one whose `f` is 7
# doesn't.
fn plus_one -> f : f~(Nat -> List Value -> Option Value)
    \_ vs ->
        match vs
            [Integer n] -> Some (Integer (n + 1))
            _           -> None

check model.holds_at (context F) (model_with plus_one NO_ARRAYS (\_ _ -> Countable) 10) f_axiom [Integer 3]
check not (model.holds_at (context F) (with_x (Integer 7)) f_axiom [Integer 3])

# ── The model's arrays, one family per sort ──────────────────────────────────

let A = b"(set-logic ALL)(assert (forall ((a (Array Int Int))) (= (select a 0) 0)))(assert (forall ((b (Array Int Bool))) (select b 0)))(assert (not false))(check-sat)"

# Integer arrays are all 0, Boolean ones all true: both axioms hold at the
# model's arrays of their sort, and an array of another sort isn't one they
# speak of.
fn by_sort -> f : f~(Sort -> ArrayId -> Value -> Option Value)
    \s _ _ ->
        match s
            Arr _ Int  -> Some (Integer 0)
            Arr _ Bool -> Some (Truth True)
            _          -> None

let ARRAYS = model_with (\_ _ -> None) by_sort (\_ _ -> Countable) 10

check model.holds_at (context A) ARRAYS (axiom A 0) [ArrayElem (Arr Int Int) (Named 0)]
check model.holds_at (context A) ARRAYS (axiom A 1) [ArrayElem (Arr Int Bool) (Named 0)]
check model.holds_at (context A) ARRAYS (axiom A 0) [ArrayElem (Arr Int Bool) (Named 0)]

# ── Domains of uninterpreted sorts ───────────────────────────────────────────

let U = b"(set-logic ALL)(declare-sort U 0)(declare-const a U)(assert (forall ((u U)) (= u a)))(assert (not false))(check-sat)"

fn domain_of d -> m : d~Domain, m~Model
    model_with (constant (Element 0)) NO_ARRAYS (\_ _ -> d) 10

# With one element, every `u` is `a`; `Element 1` isn't in the domain.
check model.holds_at (context U) (domain_of (UpTo 0)) (axiom U 0) [Element 0]
check model.holds_at (context U) (domain_of (UpTo 0)) (axiom U 0) [Element 1]
# With countably many, `Element 1` is one, and isn't `a`.
check not (model.holds_at (context U) (domain_of Countable) (axiom U 0) [Element 1])

# ── A `lambda` is the array the model names ──────────────────────────────────

let L = b"(set-logic ALL)(assert (= (select (lambda ((i Int)) i) 1) 1))(assert (not false))(check-sat)"

fn fuel n -> m : n~Nat, m~Model
    model_with (\_ _ -> None) NO_ARRAYS (\_ _ -> Countable) n

# A model that names every `lambda` `Named 0`, whose `select` is `id`: the
# identity array, or another.
fn lambda_model id -> m : id~(Value -> Value), m~Model
    let b = fuel 0
    let select = \_ _ i -> Some (id i)
    let lambda = \_ _ _ _ _ -> Some (Named 0)
    Model b.funs select b.const b.store b.sum lambda b.array_domain b.differ b.div_zero b.mod_zero b.nth_out b.wrong_sel b.domain b.fuel

check model.eval (context L) (fuel 0) (fact L 0) == Err LambdaNotGiven
# The meaning evaluates no body, so it needs no fuel.
check model.eval (context L) (lambda_model (\i -> i)) (fact L 0) == Ok (Truth True)
# A model may name it an array that isn't its body: `lambda_law` is what
# rules that out.
check model.eval (context L) (lambda_model (\_ -> Integer 0)) (fact L 0) == Ok (Truth False)
check model.lambda_law (context L) (lambda_model (\i -> i)) (Arr Int Int) [] [] Int (Var 0) (Integer 1)
check not (model.lambda_law (context L) (lambda_model (\_ -> Integer 0)) (Arr Int Int) [] [] Int (Var 0) (Integer 1))

# Comparing values uses no fuel.
let ONE = b"(set-logic ALL)(assert (= 1 1))(assert (not false))(check-sat)"

check model.eval (context ONE) (fuel 0) (fact ONE 0) == Ok (Truth True)

# ── Unfolding: fuel, and parameters in order ─────────────────────────────────

let G = b"(set-logic ALL)(define-fun-rec down ((n Int)) Int (ite (<= n 0) 0 (down (- n 1))))(define-fun-rec sub ((a Int) (b Int)) Int (- a b))(assert (= (down 10) 0))(assert (= (sub 5 3) 2))(assert (not false))(check-sat)"

fn marked src -> c : src~Bytes, c~Context
    match models.marked (context src)
        Ok c  -> c
        Err _ -> term.empty

# `down 10` unfolds eleven times: not within 3 levels, within 20.
check model.eval_unfolding (marked G) (fuel 3) (fact G 0) == Err OutOfFuel
check model.eval_unfolding (marked G) (fuel 20) (fact G 0) == Ok (Truth True)
# Two parameters, in order: `sub 5 3` is 2, not -2.
check model.eval_unfolding (marked G) (fuel 2) (fact G 1) == Ok (Truth True)

fn def_at src k -> d : src~Bytes, k~Nat, d~(Nat, Def)
    match list.head (list.drop k (term.defs (context src)))
        Some x -> x
        None   -> (0, Def b"" [] Int (App (Num 0) []) False)

fn axiom_of src k -> a : src~Bytes, k~Nat, a~Axiom
    let (n, d) = def_at src k
    model.definition_axiom n d

# A model whose `sub` is `a - b` satisfies its definition at (5, 3); one
# whose `sub` is `b - a` doesn't.
fn sub_by f -> m : f~(Int -> Int -> Int), m~Model
    let funs = \_ vs ->
        match vs
            [Integer a, Integer b] -> Some (Integer (f a b))
            _                      -> None
    model_with funs NO_ARRAYS (\_ _ -> Countable) 10

check model.holds_at (context G) (sub_by (\a b -> a - b)) (axiom_of G 1) [Integer 5, Integer 3]
check not (model.holds_at (context G) (sub_by (\a b -> b - a)) (axiom_of G 1) [Integer 5, Integer 3])

# An axiom over two variables, in order.
let TWO = b"(set-logic ALL)(assert (forall ((a Int) (b Int)) (> a b)))(assert (not false))(check-sat)"

check model.holds_at (context TWO) NOTHING (axiom TWO 0) [Integer 2, Integer 1]
check not (model.holds_at (context TWO) NOTHING (axiom TWO 0) [Integer 1, Integer 2])

# ── Arrays given to what the model defines ───────────────────────────────────

let FA = b"(set-logic ALL)(declare-fun f ((Array Int Int)) Int)(assert (= (f ((as const (Array Int Int)) 0)) 0))(assert (not false))(check-sat)"

# A model that doesn't name the constant array: not given.
check model.eval (context FA) (with_x (Integer 0)) (fact FA 0) == Err (NotGiven (ConstArr (Arr Int Int)))
# Named by its normal form, it is an argument like any other.
check model.holds (context FA) (model.normal_arrays (term.signature (context FA)) (with_x (Integer 0))) (fact FA 0)

let MA = b"(set-logic ALL)(declare-const a (Array (Array Int Int) Int))(assert (= (select a ((as const (Array Int Int)) 0)) 0))(assert (not false))(check-sat)"

fn with_model_array -> m : m~Model
    let m = model_with (constant (ArrayElem (Arr (Arr Int Int) Int) (Named 0))) (\_ _ _ -> Some (Integer 0)) (\_ _ -> Countable) 10
    model.normal_arrays (term.signature (context MA)) m

check model.holds (context MA) with_model_array (fact MA 0)

# ── What the model gives must be of the sort needed ──────────────────────────

let SA = b"(set-logic ALL)(declare-const a (Array Int Int))(assert (= (select a 0) 0))(assert (not false))(check-sat)"

fn array_giving v -> m : v~Value, m~Model
    model_with (constant (ArrayElem (Arr Int Int) (Named 0))) (\_ _ _ -> Some v) (\_ _ -> Countable) 10

check model.holds (context SA) (array_giving (Integer 0)) (fact SA 0)
check model.eval (context SA) (array_giving (Truth True)) (fact SA 0) == Err model.WrongSort

let NTH = b"(set-logic ALL)(assert (= (seq.nth (as seq.empty (Seq Int)) 0) 0))(assert (not false))(check-sat)"

fn nth_giving v -> m : v~Value, m~Model
    model.without_arrays (\_ _ -> None) (\_ -> None) (\_ -> None) (\_ _ _ -> Some v) (\_ _ _ _ _ -> None) (\_ _ -> Countable) 10

check model.holds (context NTH) (nth_giving (Integer 0)) (fact NTH 0)
check model.eval (context NTH) (nth_giving (Truth False)) (fact NTH 0) == Err model.WrongSort

let SEL = b"(set-logic ALL)(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))(assert (= (hd nil) 0))(assert (not false))(check-sat)"

fn sel_giving v -> m : v~Value, m~Model
    model.without_arrays (\_ _ -> None) (\_ -> None) (\_ -> None) (\_ _ _ -> None) (\_ _ _ _ _ -> Some v) (\_ _ -> Countable) 10

check model.holds (context SEL) (sel_giving (Integer 0)) (fact SEL 0)
check model.eval (context SEL) (sel_giving (Truth False)) (fact SEL 0) == Err model.WrongSort

# An element outside the sort's domain isn't one of its values.
let EL = b"(set-logic ALL)(declare-sort U 0)(declare-const a U)(assert (= a a))(assert (not false))(check-sat)"

fn element_in n d -> m : n~Nat, d~Domain, m~Model
    model_with (constant (Element n)) NO_ARRAYS (\_ _ -> d) 10

check model.holds (context EL) (element_in 0 (UpTo 0)) (fact EL 0)
check model.eval (context EL) (element_in 5 (UpTo 0)) (fact EL 0) == Err model.WrongSort

# ── `refutes` with an axiom ──────────────────────────────────────────────────

# `x = 1` satisfies the axiom and the fact, and the goal `false` fails;
# still no `refutes`, since the axiom is a `forall` it can't evaluate.
let AX = b"(set-logic ALL)(declare-const x Int)(assert (forall ((n Int)) (=> (= n x) (> n 0))))(assert (= x 1))(assert (not false))(check-sat)"

fn ax_refuted -> r : r~Bool
    match query AX
        Some q -> model.refutes q.context q.goal (with_x (Integer 1))
        None   -> True

check model.holds (context AX) (with_x (Integer 1)) (fact AX 0)
check not ax_refuted

# Without the axiom, the same model refutes.
let NOAX = b"(set-logic ALL)(declare-const x Int)(assert (= x 1))(assert (not false))(check-sat)"

fn noax_refuted -> r : r~Bool
    match query NOAX
        Some q -> model.refutes q.context q.goal (with_x (Integer 1))
        None   -> False

check noax_refuted

# Constant arrays over an uninterpreted index: named by their constants,
# as at every index sort, so different constants are different arrays (no
# sort is empty). A model may name them otherwise: one that names each
# constant by its value makes them different elements too.
let CU = b"(set-logic ALL)(declare-sort U 0)(assert (not (= ((as const (Array U Int)) 0) ((as const (Array U Int)) 1))))(assert (not false))(check-sat)"

fn by_value -> m : m~Model
    let b = NOTHING
    let const = \_ v ->
        match v
            Integer n -> Some (Named (if n < 0 then 0 else n))
            _         -> None
    Model b.funs b.select const b.store b.sum b.lambda b.array_domain b.differ b.div_zero b.mod_zero b.nth_out b.wrong_sel b.domain b.fuel

check model.holds (context CU) (model.normal_arrays (term.signature (context CU)) NOTHING) (fact CU 0)
check model.holds (context CU) by_value (fact CU 0)

# ── Normal forms ─────────────────────────────────────────────────────────────

let II = Arr Int Int
let BI = Arr Bool Int

fn konst s v -> a : s~Sort, v~Value, a~Value
    match model.const_array term.empty_sig (\_ _ -> Countable) s v
        Some x -> x
        None   -> Truth False

fn term_seq xs -> v : xs~List Value, v~Value
    model.Sequence xs

fn put s a j x -> r : s~Sort, a~Value, j~Value, x~Value, r~Value
    match model.store_array term.empty_sig (\_ _ -> Countable) s a j x
        Some y -> y
        None   -> Truth False

let ZERO = konst II (Integer 0)

# Stores at different indices, in either order, name one array.
check put II (put II ZERO (Integer 1) (Integer 5)) (Integer 2) (Integer 6) == put II (put II ZERO (Integer 2) (Integer 6)) (Integer 1) (Integer 5)
# A later store at an index hides the earlier one.
check put II (put II ZERO (Integer 1) (Integer 5)) (Integer 1) (Integer 7) == put II ZERO (Integer 1) (Integer 7)
# Storing the constant changes nothing.
check put II ZERO (Integer 1) (Integer 0) == ZERO
check put II (put II ZERO (Integer 1) (Integer 5)) (Integer 1) (Integer 0) == ZERO
# A `Bool` index with both indices stored: the constant doesn't matter.
check put BI (put BI (konst BI (Integer 0)) (Truth False) (Integer 1)) (Truth True) (Integer 1) == konst BI (Integer 1)
check put BI (konst BI (Integer 0)) (Truth False) (Integer 3) == put BI (konst BI (Integer 3)) (Truth True) (Integer 0)
# At an uninterpreted index only constant arrays are named: a store has no
# normal form, since the sort may be finite.
let UI = Arr (Unin 0 []) Int

check model.const_array (term.signature (context CU)) (\_ _ -> UpTo 1) UI (Integer 0) != None
check model.store_array (term.signature (context CU)) (\_ _ -> UpTo 1) UI (konst UI (Integer 0)) (Element 1) (Integer 1) != None
# A sequence index is infinite for any element sort with a value.
let SI = Arr (term.Seq (Unin 0 [])) Int

check put SI (konst SI (Integer 0)) (term_seq [Element 0]) (Integer 1) != Truth False

# ── `refutes` compares only what it can ──────────────────────────────────────

let AB = b"(set-logic ALL)(declare-const a (Array Int Int))(declare-const b (Array Int Int))(assert (not (= a b)))(assert (not false))(check-sat)"

fn named_ab -> m : m~Model
    let funs = \f _ -> Some (ArrayElem II (Named f))
    model.normal_arrays (term.signature (context AB)) (model_with funs (\_ _ _ -> Some (Integer 0)) (\_ _ -> Countable) 10)

# In the meaning `a` and `b` are different elements; in `refutes`, arrays Z3
# printed without a normal form may be the same function.
check model.holds (context AB) named_ab (fact AB 0)
check model.eval_unfolding (context AB) named_ab (fact AB 0) == Err ArraysCompared

fn normal_ab -> m : m~Model
    let funs = \f _ -> Some (if f == 0 then ZERO else put II ZERO (Integer 3) (Integer 1))
    model.normal_arrays (term.signature (context AB)) (model_with funs NO_ARRAYS (\_ _ -> Countable) 10)

# Normal forms compare in `refutes` too.
check model.eval_unfolding (context AB) normal_ab (fact AB 0) == Ok (Truth True)

# ── The `arrays_ok` laws, at points ──────────────────────────────────────────

let N = model.normal_arrays (term.signature (context AB)) NOTHING

fn id_of a -> r : a~Value, r~ArrayId
    match a
        ArrayElem _ x -> x
        _             -> Named 0

let FIVE = put II ZERO (Integer 1) (Integer 5)

# `normal_arrays` keeps the laws: read over write, at the index and away
# from it; constant arrays; sums; extensionality, with bases that agree and
# that differ.
check model.store_law (context AB) N II (id_of ZERO) (Integer 1) (Integer 5) (Integer 1)
check model.store_law (context AB) N II (id_of FIVE) (Integer 2) (Integer 6) (Integer 1)
check model.const_law (context AB) N II (Integer 4) (Integer 9)
check model.sum_law (context AB) N II (id_of FIVE) (id_of FIVE) (Integer 1)
check model.ext_law (context AB) N II (id_of ZERO) (id_of FIVE)
check model.ext_law (context AB) N II (id_of ZERO) (id_of (konst II (Integer 1)))
check model.ext_law (context AB) N BI (id_of (konst BI (Integer 0))) (id_of (put BI (konst BI (Integer 0)) (Truth True) (Integer 1)))

# A model whose `store` forgets the store breaks read over write.
fn forgetful -> m : m~Model
    let store = \_ id _ _ -> Some id
    Model N.funs N.select N.const store N.sum N.lambda N.array_domain N.differ N.div_zero N.mod_zero N.nth_out N.wrong_sel N.domain N.fuel

check not (model.store_law (context AB) forgetful II (id_of ZERO) (Integer 1) (Integer 5) (Integer 1))
