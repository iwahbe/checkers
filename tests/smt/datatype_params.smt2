(set-logic ALL)
(declare-datatypes ((L 1)) (((Nil) (Cons (hd Int) (tl (L Int))))))
(assert (not true))
(check-sat)
