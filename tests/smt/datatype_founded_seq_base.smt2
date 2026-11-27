(set-logic ALL)
; A sequence of itself beside a constructor with no fields: founded, and
; Z3 5.3.3 accepts it.
(declare-datatypes ((D 0)) (((K (f (Seq D))) (B))))
(declare-const x D)
(assert (= x (K (seq.unit B))))
(assert (not false))
(check-sat)
