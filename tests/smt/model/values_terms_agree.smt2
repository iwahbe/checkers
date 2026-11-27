(set-logic ALL)
; The values of terms that aren't constants are read and must be what the
; other values make them.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x (= x 1) (+ x 1)))
