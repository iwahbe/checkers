(set-logic ALL)
; A term asked twice, printed with one value twice, is read.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x x))
