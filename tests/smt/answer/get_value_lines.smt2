(set-logic ALL)
(declare-const x Int)
(assert (not (= x x)))
(check-sat)
(get-value
 (x)
 )
