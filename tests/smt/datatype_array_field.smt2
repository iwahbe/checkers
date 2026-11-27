(set-logic ALL)
; A datatype in the index of an array in its own constructor: with arrays as all
; functions there is no such set (Cantor); Z3 rejects it ("not co-variant").
(declare-datatypes ((T 0)) (((mk (x (Array T Int))))))
(declare-const c T)
(assert (not false))
(check-sat)
