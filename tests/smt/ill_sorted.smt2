(set-logic ALL)
(declare-const x Int)
(assert (not (= (+ x true) 1)))
(check-sat)
