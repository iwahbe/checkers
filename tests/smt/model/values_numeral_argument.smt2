(set-logic ALL)
; `(f 1)` printed as asked is read.
(declare-fun f (Int) Int)
(assert (= (f 1) 5))
(assert (not false))
(check-sat)
(get-value ((f 1)))
