; The query of `full_refutes_lambda_goal` without its `lambda`. Z3 5.3.3:
; sat, and `refutes` takes its model.
(set-logic ALL)
(declare-const y Int)
(assert (= y 1))
(assert (not (ite (= y 1) false (= y y))))
(check-sat)
