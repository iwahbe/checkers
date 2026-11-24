(set-logic ALL)
; Each needs the other and neither has a base: no values.
(declare-datatypes ((Odd 0) (Even 0)) (((o (e Even))) ((v (d Odd)))))
(declare-const c Odd)
(assert (not false))
(check-sat)
