(set-logic ALL)
; get-model doesn't print a selector applied to another constructor's value.
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-const xs L)
(assert (= xs nil))
(assert (= (hd xs) 5))
(assert (not false))
(check-sat)
