(set-logic ALL)
; `(W Int T)` puts `T` in an array's index through `W`'s second parameter. Rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((W 2)) ((par (X Y) ((w (x X) (f (Array Y Int)))))))
(declare-datatypes ((T 0)) (((leaf) (mk (wt (W Int T))))))
(assert (not false))
(check-sat)
