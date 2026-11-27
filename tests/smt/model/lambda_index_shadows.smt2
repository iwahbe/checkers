(set-logic ALL)
; The answer's `lambda` binds `x`, which is also a constant of the model:
; inside the `lambda` `x` is its index, and an array whose value uses its
; index has no normal form, so `a` isn't read (Z3: adding
; `(= a (lambda ((x Int)) x))` makes it unsat).
(declare-const x Int)
(declare-const a (Array Int Int))
(assert (= x 5))
(assert (= (select a 7) 5))
(assert (not false))
(check-sat)
