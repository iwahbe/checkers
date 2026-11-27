(set-logic ALL)
; `T` in an index of arrays to a sort with one value: refused all the same (as Z3 refuses it).
(declare-datatypes ((Unit 0)) (((unit))))
(declare-datatypes ((T 0)) (((mk (f (Array T Unit))))))
(assert (not false))
(check-sat)
