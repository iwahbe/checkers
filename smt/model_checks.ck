# model_checks.ck — `check`s of `smt.model`'s meaning (`AsGiven`), which
# `main model` and `main models` don't run: `holds`, `fails`, `holds_all`,
# `holds_at` (with the model's arrays, one family per sort, and the domain of
# an uninterpreted sort), `definition_axiom`, fuel, and terms that aren't
# the context's. Every `ckc check` of this file runs them.

module model_checks

import std.list
import smtlib (Query)
import term (Sort, Int, Bool, Arr, Unin, Context, Term, App, Prim, Num, Boolean, And, Axiom, Def)
import model (Value, Truth, Integer, Element, ModelArray, Model, Domain, UpTo, Countable, Unknown, OutOfFuel)
import model (NotTerminating, IllSorted)
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

# A model: the functions `funs`, the arrays `arrays`, the domains `domain`,
# with `fuel`; it says nothing else.
fn model_with funs arrays domain fuel -> m : funs~(Nat -> List Value -> Option Value),
                                             arrays~(Sort -> Nat -> Value -> Option Value),
                                             domain~(Nat -> List Sort -> Domain), fuel~Nat, m~Model
    Model funs arrays (\_ -> None) (\_ -> None) (\_ _ _ -> None) (\_ _ _ _ _ -> None) domain fuel

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
fn by_sort -> f : f~(Sort -> Nat -> Value -> Option Value)
    \s _ _ ->
        match s
            Arr _ Int  -> Some (Integer 0)
            Arr _ Bool -> Some (Truth True)
            _          -> None

let ARRAYS = model_with (\_ _ -> None) by_sort (\_ _ -> Countable) 10

check model.holds_at (context A) ARRAYS (axiom A 0) [ModelArray (Arr Int Int) 0]
check model.holds_at (context A) ARRAYS (axiom A 1) [ModelArray (Arr Int Bool) 0]
check model.holds_at (context A) ARRAYS (axiom A 0) [ModelArray (Arr Int Bool) 0]

# ── Domains of uninterpreted sorts ───────────────────────────────────────────

let U = b"(set-logic ALL)(declare-sort U 0)(declare-const a U)(assert (forall ((u U)) (= u a)))(assert (not false))(check-sat)"

fn domain_of d -> m : d~Domain, m~Model
    model_with (constant (Element 0)) NO_ARRAYS (\_ _ -> d) 10

# With one element, every `u` is `a`; `Element 1` isn't in the domain.
check model.holds_at (context U) (domain_of (UpTo 0)) (axiom U 0) [Element 0]
check model.holds_at (context U) (domain_of (UpTo 0)) (axiom U 0) [Element 1]
# With countably many, `Element 1` is one, and isn't `a`.
check not (model.holds_at (context U) (domain_of Countable) (axiom U 0) [Element 1])

# ── Fuel ─────────────────────────────────────────────────────────────────────

let L = b"(set-logic ALL)(assert (= (select (lambda ((i Int)) i) 1) 1))(assert (not false))(check-sat)"

fn fuel n -> m : n~Nat, m~Model
    model_with (\_ _ -> None) NO_ARRAYS (\_ _ -> Countable) n

check model.eval (context L) (fuel 0) (fact L 0) == Err OutOfFuel
check model.eval (context L) (fuel 1) (fact L 0) == Ok (Truth True)

# Comparing data uses no fuel.
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

# The model would say 0 for every argument, but isn't asked about an array.
check model.eval (context FA) (with_x (Integer 0)) (fact FA 0) == Err model.ArraysCompared

let MA = b"(set-logic ALL)(declare-const a (Array (Array Int Int) Int))(assert (= (select a ((as const (Array Int Int)) 0)) 0))(assert (not false))(check-sat)"

fn with_model_array -> m : m~Model
    model_with (constant (ModelArray (Arr (Arr Int Int) Int) 0)) (\_ _ _ -> Some (Integer 0)) (\_ _ -> Countable) 10

check model.eval (context MA) with_model_array (fact MA 0) == Err model.ArraysCompared

# ── What the model gives must be of the sort needed ──────────────────────────

let SA = b"(set-logic ALL)(declare-const a (Array Int Int))(assert (= (select a 0) 0))(assert (not false))(check-sat)"

fn array_giving v -> m : v~Value, m~Model
    model_with (constant (ModelArray (Arr Int Int) 0)) (\_ _ _ -> Some v) (\_ _ -> Countable) 10

check model.holds (context SA) (array_giving (Integer 0)) (fact SA 0)
check model.eval (context SA) (array_giving (Truth True)) (fact SA 0) == Err model.WrongSort

let NTH = b"(set-logic ALL)(assert (= (seq.nth (as seq.empty (Seq Int)) 0) 0))(assert (not false))(check-sat)"

fn nth_giving v -> m : v~Value, m~Model
    Model (\_ _ -> None) NO_ARRAYS (\_ -> None) (\_ -> None) (\_ _ _ -> Some v) (\_ _ _ _ _ -> None) (\_ _ -> Countable) 10

check model.holds (context NTH) (nth_giving (Integer 0)) (fact NTH 0)
check model.eval (context NTH) (nth_giving (Truth False)) (fact NTH 0) == Err model.WrongSort

let SEL = b"(set-logic ALL)(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))(assert (= (hd nil) 0))(assert (not false))(check-sat)"

fn sel_giving v -> m : v~Value, m~Model
    Model (\_ _ -> None) NO_ARRAYS (\_ -> None) (\_ -> None) (\_ _ _ -> None) (\_ _ _ _ _ -> Some v) (\_ _ -> Countable) 10

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
