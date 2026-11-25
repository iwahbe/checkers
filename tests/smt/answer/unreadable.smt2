(set-logic ALL)
(declare-const x Int)
(assert (not (= x "a")))
(check-sat)
