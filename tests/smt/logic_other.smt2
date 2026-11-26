(set-logic QF_UF)
(declare-const x Int)
(assert (not (= x 1)))
(check-sat)
