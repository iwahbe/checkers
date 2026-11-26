(set-logic ALL)
(declare-const x Int)
(assert (not (let ((v 1)) (= (v) x))))
(check-sat)
