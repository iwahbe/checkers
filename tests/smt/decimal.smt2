(set-logic ALL)
(declare-const x Int)
(assert (not (= x 1.5)))
(check-sat)
