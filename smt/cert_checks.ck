# cert_checks.ck — `check`s of `smt.cert`: refutations `checks` accepts,
# each changed in one way it must reject (a hint that leaves two literals
# open, a clause number past those added, a last clause that isn't empty,
# an atom that isn't a closed `Bool`, a structure clause that isn't one),
# and what `smt.solve` finds by unit propagation. Every `ckc check` of this
# file runs them.

module cert_checks

import std.list
import smtlib (Query)
import term (Term, Context, Var, App, Prim, Num, Boolean, Fun, Eq)
import cert (Refutation, Lit, Fact, NotGoal, Structure, Resolve)
import model (Model, Truth, Countable)
import solve (Limits, Proved, GaveUp, Incomplete)

fn query src -> q : src~Bytes, q~Option Query
    match smtlib.parse src
        Ok x  -> Some x
        Err _ -> None

fn context src -> c : src~Bytes, c~Context
    match query src
        Some q -> q.context
        None   -> term.empty

fn goal src -> t : src~Bytes, t~Term
    match query src
        Some q -> q.goal
        None   -> App (Boolean False) []

fn checks src steps -> r : src~Bytes, steps~List cert.Step, r~Bool
    cert.checks (context src) (goal src) (Refutation steps)

# `p` is the 0th function, `q` the 1st. Facts: `(and p q)`. Goal: `q`.
let AND = b"(set-logic ALL)(declare-const p Bool)(declare-const q Bool)(assert (and p q))(assert (not q))(check-sat)"
let P = App (Fun 0) []
let Q = App (Fun 1) []
let PQ = App (Prim term.And) [P, Q]

# `[p ∧ q]`, `[¬q]`, `[¬(p ∧ q), q]` (clause 2 of the conjunction), then the
# empty clause from 0, 2, 1.
let GOOD = [Fact 0, NotGoal, Structure PQ 2, Resolve [] [0, 2, 1]]

check checks AND GOOD
# The hints out of order: clause 2 has two literals open first.
check not (checks AND [Fact 0, NotGoal, Structure PQ 2, Resolve [] [2, 0, 1]])
# A clause number past those added.
check not (checks AND [Fact 0, NotGoal, Structure PQ 2, Resolve [] [0, 2, 7]])
# The last clause isn't empty.
check not (checks AND [Fact 0, NotGoal, Structure PQ 2])
# No step at all.
check not (checks AND [])
# A clause derived first, then used: `[q]` from 0 and 2, then the empty one.
check checks AND [Fact 0, NotGoal, Structure PQ 2, Resolve [Lit True Q] [0, 2], Resolve [] [3, 1]]
# A derived clause that doesn't follow: `[p]` from `[¬q]` alone.
check not (checks AND [Fact 0, NotGoal, Structure PQ 2, Resolve [Lit True P] [1], Resolve [] [3, 1]])
# A structure clause that isn't one of the term's: the conjunction has
# clauses 0 to 2.
check not (checks AND [Fact 0, NotGoal, Structure PQ 3, Resolve [] [0, 2, 1]])
# An atom that isn't a closed `Bool`: `(= 1 1 1)` has no sort, `1` isn't a
# `Bool`, and `Var 0` isn't closed.
check not (checks AND [Resolve [Lit True (App (Prim Eq) [App (Num 1) [], App (Num 1) [], App (Num 1) []])] []])
check not (checks AND [Resolve [Lit True (App (Num 1) [])] []])
check not (checks AND [Structure (App (Prim term.Not) [Var 0]) 0, Resolve [] [0]])
# A fact that isn't there.
check not (checks AND [Fact 1, NotGoal, Structure PQ 2, Resolve [] [0, 2, 1]])

fn solved src -> v : src~Bytes, v~solve.Verdict
    let out = solve.solve (solve.prepare (context src)) (goal src) (Limits 1000)
    solve.verdict out.answer

check solved AND == Proved
# Satisfiable: no refutation.
check solved b"(set-logic ALL)(declare-const p Bool)(declare-const q Bool)(assert (or p q))(assert (not p))(check-sat)" == GaveUp Incomplete
# Through `let`, `ite`, `=>` and `=` between `Bool`s.
check solved b"(set-logic ALL)(declare-const p Bool)(declare-const q Bool)(assert (let ((a p)) (and a q)))(assert (not (let ((a p)) q)))(check-sat)" == Proved
check solved b"(set-logic ALL)(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)(assert (=> p q))(assert (= q r))(assert (ite p (not r) false))(assert (not false))(check-sat)" == Proved
# Out of work.
check solve.verdict (solve.solve (solve.prepare (context AND)) (goal AND) (Limits 2)).answer == GaveUp solve.OutOfWork
# The goal and the cited fact are among the terms used.
check cert.terms (context AND) (goal AND) (Refutation GOOD) == [Q, PQ, Q, PQ, Q]

# The premises of `checks_sound` can be met for an accepted refutation: in
# the model with `p` and `q` true, the facts hold and every term used has a
# value of its sort. (The context has no axioms, definitions or arrays, so
# the other premises ask nothing.)
fn everything_true -> m : m~Model
    let funs = \_ _ -> Some (Truth True)
    model.without_arrays funs (\_ -> None) (\_ -> None) (\_ _ _ -> None) (\_ _ _ _ _ -> None) (\_ _ -> Countable) 10

let BOTH = everything_true

check model.holds_all (context AND) BOTH (term.facts (context AND))
check list.all (\t -> model.has_value (context AND) BOTH t) (cert.terms (context AND) (goal AND) (Refutation GOOD))
check term.axioms (context AND) == [] and term.defs (context AND) == []
check model.holds (context AND) BOTH (goal AND)
# A goal that isn't a closed `Bool` term is never refuted.
check not (cert.checks (context AND) (App (Num 1) []) (Refutation GOOD))
