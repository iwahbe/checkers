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
