(set-logic ALL)
(define-fun-rec f ((n Int)) Int (ite (= n 0) true (f (- n 1))))
(assert (not (= (f 1) 1)))
(check-sat)
