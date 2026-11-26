(set-logic ALL)
; Each holds the other, one through a sequence. Z3 5.3.3 refuses the
; group ("datatype is not well-founded").
(declare-datatypes ((D 0) (E 0)) (((K (f (Seq E)))) ((L (g D)))))
(assert (not false))
(check-sat)
