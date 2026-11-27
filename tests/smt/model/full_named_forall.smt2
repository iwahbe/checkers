(set-logic ALL)
; Z3 prints a named assertion's value, here a `forall` with a pattern: it
; is read, and not evaluated.
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (! (forall ((y Int)) (! (>= (f y) 0) :pattern ((f y)))) :named g))
(assert (= x 1))
(assert (not false))
(check-sat)
