(set-logic ALL)
; Elements of an uninterpreted sort, as Z3 names them.
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(assert (not (= a b)))
(assert (not false))
(check-sat)
(get-value (a b))
