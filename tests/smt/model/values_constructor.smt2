(set-logic ALL)
; The value `nil` as Z3 prints it is read.
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-const l L)
(assert (= l nil))
(assert (not false))
(check-sat)
(get-value (l))
