(set-logic ALL)
; The same through a datatype declared before, whose parameter is inside
; an array's index.
(declare-datatypes ((F 1)) ((par (A) ((f (g (Array A Int)))))))
(declare-datatypes ((T 0)) (((mk (x (F T))))))
(declare-const c T)
(assert (not false))
(check-sat)
