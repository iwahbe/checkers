(set-logic ALL)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
; A selector of another constructor's value is unspecified: the model says it.
(assert (= (hd nil) 5))
(assert (= (tl nil) (cons 1 nil)))
(assert (not false))
(check-sat)
(get-value ((hd nil) (tl nil)))
