(set-logic ALL)
(declare-const x Int)
(assert (not (distinct x 1 2)))
(check-sat)
