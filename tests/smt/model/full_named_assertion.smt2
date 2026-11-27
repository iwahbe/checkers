(set-logic ALL)
; A named assertion's printed value is read, and is what the assertion
; gives.
(declare-const x Int)
(assert (! (> x 0) :named a1))
(assert (= x 5))
(assert (not false))
(check-sat)
