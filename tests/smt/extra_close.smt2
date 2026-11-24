(set-logic ALL)
(declare-const x Int))
(assert (not (= x 1)))
(check-sat)
