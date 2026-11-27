(set-logic ALL)
; A query with a `forall`: its facts without a quantifier are still
; evaluated; here one is false in the answer (edited), and the run fails.
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (forall ((y Int)) (= (f y) y)))
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x))
