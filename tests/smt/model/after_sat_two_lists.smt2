(set-logic ALL)
; Two value lists after `sat`, where the query asks for one: not read.
(declare-const x Int)
(assert (= x 2))
(assert (not false))
(check-sat)
(get-value (x))
