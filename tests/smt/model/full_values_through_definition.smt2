(set-logic ALL)
; With the values and the model: a value through the query's definition,
; and one for `(div x 0)`, which the model doesn't print, are read; each
; is compared where the model gives its term a value.
(define-fun g ((p Int)) Int (+ p 1))
(declare-const x Int)
(assert (= x 4))
(assert (not false))
(check-sat)
(get-value (x (g x) (div x 0)))
