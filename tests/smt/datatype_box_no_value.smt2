(set-logic ALL)
; A value of `T` needs one inside `(Box T)`: none. Rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((Box 1)) ((par (A) ((box (unbox A))))))
(declare-datatypes ((T 0)) (((mk (b (Box T))))))
(assert (not false))
(check-sat)
