(set-logic ALL)
; A definition isn't printed: it is run as its body.
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(define-fun-rec size ((xs L)) Int (ite (is-nil xs) 0 (+ 1 (size (tl xs)))))
(declare-const xs L)
(assert (= (size xs) 3))
(assert (not false))
(check-sat)
