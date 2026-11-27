(set-logic ALL)
; A function's value at a constant's printed value: `(f x)` gives `f`
; at 1, so `(= (f x) 7)` is determined.
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= x 1))
(assert (= (f x) 7))
(assert (not false))
(check-sat)
(get-value (x (f x)))
