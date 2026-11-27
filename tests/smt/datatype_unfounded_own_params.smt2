(set-logic ALL)
; A parametric datatype holding itself at its own parameter, inside a
; sequence, beside a field of the parameter. Z3 5.3.3 refuses it
; ("datatype is not well-founded").
(declare-datatypes ((D 1)) ((par (A) ((K (f A) (g (Seq (D A))))))))
(assert (not false))
(check-sat)
