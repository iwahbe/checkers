(set-logic ALL)
; A `let` in a body of Z3's model is parallel too: `b` is the outer `a`.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
