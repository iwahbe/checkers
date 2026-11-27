(set-logic ALL)
; Elements of an instance of a sort with parameters are read at that
; instance.
(declare-sort P 1)
(declare-const p (P Int))
(declare-const q (P Int))
(assert (not (= p q)))
(assert (not false))
(check-sat)
(get-value (p q))
