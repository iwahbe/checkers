(set-logic ALL)
; `(Either T Int)` has `(right 0)` without a `T`: `T` has `(mk (right 0))`. Accepted.
(declare-datatypes ((Either 2)) ((par (A B) ((left (l A)) (right (r B))))))
(declare-datatypes ((T 0)) (((mk (e (Either T Int))))))
(assert (not false))
(check-sat)
