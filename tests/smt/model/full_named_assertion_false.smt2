(set-logic ALL)
; A named assertion's printed value must be what the assertion gives: here
; it is not, and there is no model. (The answer is edited.)
(declare-const x Int)
(assert (! (> x 0) :named a1))
(assert (= x 5))
(assert (not false))
(check-sat)
