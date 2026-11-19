(set-logic ALL)
(declare-const x Int)
(assert (not (or (= x 1) (= x 2))))
(check-sat)
