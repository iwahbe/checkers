(set-logic ALL)
; A body may call a function the query defines: it is read, and not
; evaluated, so what needs it is not determined. (The answer is edited.)
(define-funs-rec ((dbl ((n Int)) Int)) ((* 2 n)))
(declare-fun g (Int) Int)
(assert (= (g 3) 6))
(assert (not false))
(check-sat)
