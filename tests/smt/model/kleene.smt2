(set-logic ALL)
; A conjunction with a false argument is false whatever the others are;
; ite evaluates only the branch it chooses.
(declare-const x Int)
(declare-const y Int)
(assert (= x 1))
(assert (not (and (= x 2) (= y 3))))
(assert (or (= x 1) (= y 3)))
(assert (= (ite (= x 1) 0 y) 0))
(assert (not false))
(check-sat)
(get-value (x))
