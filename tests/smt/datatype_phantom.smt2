(set-logic ALL)
; A parameter no field uses: `(P T)` has `p` whatever `T` is. Accepted.
(declare-datatypes ((P 1)) ((par (A) ((p)))))
(declare-datatypes ((T 0)) (((mk (x (P T))))))
(assert (not false))
(check-sat)
