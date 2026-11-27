(set-logic ALL)
; A constant array written at another sort than its constant's: not read.
(declare-const a (Array Int Int))
(assert (= (select a 0) 5))
(assert (not false))
(check-sat)
