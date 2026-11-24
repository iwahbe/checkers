(set-logic ALL)
; Under an uninterpreted sort constructor the datatype doesn't count: `U`
; may ignore its argument (`U X` one element for every `X`), so `T` has an
; interpretation. Accepted.
(declare-sort U 1)
(declare-datatypes ((T 0)) (((mk (x (Array (U T) Int))))))
(assert (not false))
(check-sat)
