(set-logic ALL)
; A value printed for a call of the query's definition is read, and must
; be what the definition gives.
(define-fun g ((p Int)) Int (+ p 1))
(declare-const x Int)
(assert (= x 4))
(assert (not false))
(check-sat)
(get-value (x (g 1)))
