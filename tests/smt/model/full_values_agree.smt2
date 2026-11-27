(set-logic ALL)
; With `(get-value …)` and the model, both are read, and each value must
; be what the model gives its term.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x))
