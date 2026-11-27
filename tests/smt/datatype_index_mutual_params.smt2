(set-logic ALL)
; `F`'s parameter reaches an index through `G`, of the same group. Rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((F 1) (G 1)) ((par (A) ((f (g (G A))))) (par (B) ((g0) (gm (h (Array B Int)))))))
(declare-datatypes ((T 0)) (((leaf) (mk (x (F T))))))
(assert (not false))
(check-sat)
