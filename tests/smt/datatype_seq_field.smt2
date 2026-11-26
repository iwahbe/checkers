(set-logic ALL)
; A datatype inside a sequence in its own constructor: `(mk [])` is a value.
; Z3 5.3.3 rejects it as not well-founded, and so does the reader.
(declare-datatypes ((T 0)) (((mk (x (Seq T))))))
(declare-const c T)
(assert (not false))
(check-sat)
