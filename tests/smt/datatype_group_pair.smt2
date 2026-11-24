(set-logic ALL)
; `A` needs `(Pair A B)`, which needs an `A`: none, though `B` has `bl`. Rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (fst X) (snd Y))))))
(declare-datatypes ((A 0) (B 0)) (((ma (p (Pair A B)))) ((bl) (mb (a A)))))
(assert (not false))
(check-sat)
