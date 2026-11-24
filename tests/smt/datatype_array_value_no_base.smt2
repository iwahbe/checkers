(set-logic ALL)
; The same without `base`: every value would need one already: none.
(declare-datatypes ((T 0)) (((mk (x (Array Int T))))))
(declare-const c T)
(assert (not false))
(check-sat)
