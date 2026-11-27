; An array of arrays read at two indices that are the same array. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-const a (Array Bool Int))
(declare-const c (Array (Array Bool Int) Int))
(assert (= (select a true) 0))
(assert (= (select a false) 0))
(assert (not (= (select c a) (select c ((as const (Array Bool Int)) 0)))))
(assert (not false))
(check-sat)
