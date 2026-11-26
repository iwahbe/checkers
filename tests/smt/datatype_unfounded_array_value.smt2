(set-logic ALL)
; Its one constructor holds an array of itself. Z3 5.3.3 refuses it
; ("datatype is not well-founded"), and it has no values.
(declare-datatypes ((D 0)) (((K (f (Array Int D))))))
(assert (not false))
(check-sat)
