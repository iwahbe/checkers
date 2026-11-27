(set-logic ALL)
; An inner `let` shadows an outer one: the value is 2, and the fact fails.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x))
