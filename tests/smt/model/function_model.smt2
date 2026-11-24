(set-logic ALL)
; A function with parameters: the model says only what was printed.
(declare-fun f (Int) Int)
(assert (= (f 3) 4))
(assert (> (f 5) 10))
(assert (not false))
(check-sat)
(get-value ((f 3)))
