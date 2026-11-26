; Named assertions: facts and axioms like any other, written back with their
; names. A named `(not …)` is a fact, not the goal.
(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (! (forall ((y Int)) (! (>= (f y) 0) :pattern ((f y)))) :named |given.0|))
(assert (! (> x 0) :named |fact.0|))
(assert (! (not (= x 3)) :named |fact 1|))
(assert (not (>= (f x) 0)))
(check-sat)
(get-unsat-core)
(get-value (x))
