(set-logic ALL)
; A datatype in an array's values, with a constructor that needs none: a
; tree with a branch for each `Int`. `ckc` writes these (`#base`).
(declare-datatypes ((T 0)) (((mk (x (Array Int T))) (base))))
(declare-const c T)
(assert (not false))
(check-sat)
