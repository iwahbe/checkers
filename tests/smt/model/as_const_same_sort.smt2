(set-logic ALL)
; A constant array written at its own sort.
(declare-const a (Array Int Int))
(assert (= (select a 0) 5))
(assert (not false))
(check-sat)
