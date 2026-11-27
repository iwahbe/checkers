(set-logic ALL)
; A term asked twice gets one value: two different values are not read.
; (The answer is edited.)
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x x))
