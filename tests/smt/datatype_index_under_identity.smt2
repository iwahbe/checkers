(set-logic ALL)
; `(Id T)` in an index is `T` in one. Rejected.
(declare-datatypes ((Id 1)) ((par (A) ((id (un A))))))
(declare-datatypes ((T 0)) (((leaf) (mk (f (Array (Id T) Int))))))
(assert (not false))
(check-sat)
