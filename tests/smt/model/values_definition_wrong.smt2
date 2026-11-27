(set-logic ALL)
; A value printed for a call of the query's definition that the definition
; doesn't give: not read. (The answer is edited.)
(define-fun g ((p Int)) Int (+ p 1))
(declare-const x Int)
(assert (= x 4))
(assert (not false))
(check-sat)
(get-value (x (g 1)))
