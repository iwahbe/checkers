(set-logic ALL)
; The answer's `lambda` binds `x`, also a constant of the model, and its
; value doesn't use it: the constant array of 3.
(declare-const x Int)
(declare-const a (Array Int Int))
(assert (= x 5))
(assert (= (select a 7) 3))
(assert (not false))
(check-sat)
