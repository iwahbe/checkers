(set-logic ALL)
; Z3's value for (div 5 0) makes the facts hold; (div 4 0) was not printed.
(declare-const x Int)
(assert (= (div 5 0) 7))
(assert (= x (div 5 0)))
(assert (or (= (div 4 0) 1) (= x 7)))
(assert (not false))
(check-sat)
(get-value (x (div 5 0)))
