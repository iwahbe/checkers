; Two arrays that agree at both indices, given to a function. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-const a (Array Bool Int))
(declare-const b (Array Bool Int))
(declare-fun f ((Array Bool Int)) Int)
(assert (= (select a true) (select b true)))
(assert (= (select a false) (select b false)))
(assert (not (= (f a) (f b))))
(assert (not false))
(check-sat)
