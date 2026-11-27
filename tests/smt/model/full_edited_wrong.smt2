(set-logic ALL)
; Z3 prints a function as an ite chain over its parameters, ending in a default.
(declare-fun f (Int) Int)
(assert (= (f 3) 4))
(assert (> (f 5) 10))
(assert (= (f 7) (f 3)))
(assert (not false))
(check-sat)
