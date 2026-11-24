(set-logic ALL)
; Mutually recursive definitions, unfolded.
(define-funs-rec ((ev ((n Int)) Bool) (od ((n Int)) Bool)) ((ite (<= n 0) true (od (- n 1))) (ite (<= n 0) false (ev (- n 1)))))
(assert (not (and (ev 4) (od 3) (not (ev 3)))))
(check-sat)
