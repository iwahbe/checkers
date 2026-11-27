; Two `lambda`s that are the same function, given to a function. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-fun f ((Array Int Int)) Int)
(assert (not (= (f (lambda ((x Int)) x)) (f (lambda ((x Int)) (+ x 0))))))
(assert (not false))
(check-sat)
