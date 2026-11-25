; An array equal to a constant one, given to a function with it. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-const a (Array Bool Int))
(declare-fun f ((Array Bool Int)) Int)
(assert (= (select a true) 0))
(assert (= (select a false) 0))
(assert (not (= (f a) (f ((as const (Array Bool Int)) 0)))))
(assert (not false))
(check-sat)
