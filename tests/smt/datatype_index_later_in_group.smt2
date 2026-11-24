(set-logic ALL)
; `T`'s field puts `U`, a later datatype of its group, in an array's index. Rejected.
(declare-datatypes ((T 0) (U 0)) (((leaf) (mt (f (Array U Int)))) ((mu (t T)))))
(assert (not false))
(check-sat)
