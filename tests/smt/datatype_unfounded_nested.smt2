(set-logic ALL)
; A sequence of a declared sort applied to a sequence of itself. Z3 5.3.3
; refuses it ("datatype is not well-founded").
(declare-sort S 1)
(declare-datatypes ((D 0)) (((K (f (Seq (S (Seq D))))))))
(assert (not false))
(check-sat)
