; A `lambda` and the constant array it equals, given to a function. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-fun f ((Array Bool Int)) Int)
(assert (not (= (f (lambda ((x Bool)) 0)) (f ((as const (Array Bool Int)) 0)))))
(assert (not false))
(check-sat)
