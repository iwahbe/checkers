(set-logic ALL)
; A `let` in a printed value is parallel: `b` is the outer `a`, 1.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x))
