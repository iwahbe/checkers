(set-logic ALL)
; The same under an array's values: rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((Fn 1)) ((par (A) ((fn (ap (Array A Int)))))))
(declare-datatypes ((G 1)) ((par (A) ((g (un (Array Int (Fn A))))))))
(declare-datatypes ((T 0)) (((mk (x (G T))))))
(assert (not false))
(check-sat)
