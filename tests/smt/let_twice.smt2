(set-logic ALL)
(declare-const x Int)
(assert (not (= x (let ((a 1) (a 2)) a))))
(check-sat)
