(set-logic ALL)
(declare-const x Int)
(assert (not (let ((seq.empty 1)) (= seq.empty x))))
(check-sat)
