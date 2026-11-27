(set-logic ALL)
; An instance of a sort with parameters has a universe of its own, its
; elements spelled by the sort's name.
(declare-sort P 1)
(declare-const p (P Int))
(declare-const q (P Int))
(assert (not (= p q)))
(assert (not false))
(check-sat)
