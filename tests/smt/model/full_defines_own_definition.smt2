(set-logic ALL)
; The query's own definitions are run as their bodies; a model defining
; one is not read. (The answer is edited.)
(define-fun-rec h ((n Int)) Int n)
(declare-const x Int)
(assert (= (h x) 2))
(assert (not false))
(check-sat)
