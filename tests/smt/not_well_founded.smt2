(set-logic ALL)
; Every value of `T` would need a smaller one: no value exists, and Z3
; rejects the declaration ("datatype is not well-founded").
(declare-datatypes ((T 0)) (((mk (x T)))))
(declare-const t T)
(assert (not false))
(check-sat)
