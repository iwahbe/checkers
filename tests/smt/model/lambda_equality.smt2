(set-logic ALL)
; Equal as functions, but smt.model doesn't decide equality of lambdas.
(assert (not (= (lambda ((x Int)) (+ x 1)) (lambda ((x Int)) (+ 1 x)))))
(check-sat)
