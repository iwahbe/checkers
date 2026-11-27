(set-logic ALL)
; Its one constructor holds a sequence of itself. `(K [])` is a value,
; but Z3 5.3.3 refuses the declaration ("datatype is not well-founded"),
; and so does the reader.
(declare-datatypes ((D 0)) (((K (f (Seq D))))))
(assert (not false))
(check-sat)
