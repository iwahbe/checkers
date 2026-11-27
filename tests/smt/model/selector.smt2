(set-logic ALL)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(assert (not (and (= (hd (cons 4 nil)) 4) (= (tl (cons 4 nil)) nil) (is-cons (cons 4 nil)))))
(check-sat)
