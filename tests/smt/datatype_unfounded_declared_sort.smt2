(set-logic ALL)
; Its one constructor holds a declared sort applied to itself. Z3 5.3.3
; refuses it ("datatype is not well-founded"), though `(S D)` has
; elements.
(declare-sort S 1)
(declare-datatypes ((D 0)) (((K (f (S D))))))
(assert (not false))
(check-sat)
