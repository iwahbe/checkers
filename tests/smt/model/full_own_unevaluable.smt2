(set-logic ALL)
; A printed value for the query's own constant that this reader can't
; evaluate (it calls the query's function) is said to be so.
(define-funs-rec ((dbl ((n Int)) Int)) ((* 2 n)))
(define-funs-rec ((k () Int)) ((dbl 3)))
(declare-const x Int)
(assert (= x k))
(assert (not false))
(check-sat)
