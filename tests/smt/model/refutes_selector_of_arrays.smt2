; A selector of another constructor on values holding the same array. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-datatypes ((D 0)) (((one (arr (Array Bool Int))) (two (n Int)))))
(declare-const a (Array Bool Int))
(assert (= (select a true) 0))
(assert (= (select a false) 0))
(assert (not (= (n (one a)) (n (one ((as const (Array Bool Int)) 0))))))
(assert (not false))
(check-sat)
