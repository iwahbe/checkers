; `seq.nth` out of range on sequences holding the same array. Z3 5.3.3: unsat; `refutes` must not
; accept a model telling the two apart (smt/model_checks.ck builds such models).
(set-logic ALL)
(declare-const a (Array Bool Int))
(assert (= (select a true) 0))
(assert (= (select a false) 0))
(assert (not (= (seq.nth (seq.unit a) 1) (seq.nth (seq.unit ((as const (Array Bool Int)) 0)) 1))))
(assert (not false))
(check-sat)
