(set-logic ALL)
; `(P T)` in an index: `P` uses no parameter, so `T` is not in it, but Z3 5.3.3 refuses it, and so does the reader.
(declare-datatypes ((P 1)) ((par (A) ((p)))))
(declare-datatypes ((T 0)) (((leaf) (mk (f (Array (P T) Int))))))
(assert (not false))
(check-sat)
