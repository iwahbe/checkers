(set-logic ALL)
; A group whose base is in its second datatype, in both orders. Accepted.
(declare-datatypes ((A 0) (B 0)) (((a (x B))) ((b (y A)) (bnil))))
(declare-datatypes ((D 0) (C 0)) (((dnil) (d (dy C))) ((c (cx D)))))
(assert (not false))
(check-sat)
