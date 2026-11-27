(set-logic ALL)
; A constructor with eight fields of the group, and another datatype of the
; group with a constructor with no fields. Accepted.
(declare-datatypes ((T 0) (U 0)) (((leaf) (node (a T) (b T) (c T) (d T) (e T) (f T) (g T) (h T))) ((u))))
(assert (not false))
(check-sat)
