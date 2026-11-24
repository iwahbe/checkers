(set-logic ALL)
; `(Either T T)` needs a `T` either way: none. Rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((Either 2)) ((par (A B) ((left (l A)) (right (r B))))))
(declare-datatypes ((T 0)) (((mk (e (Either T T))))))
(assert (not false))
(check-sat)
