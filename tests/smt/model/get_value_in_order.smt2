(set-logic ALL)
; The values printed for the terms asked, in order.
(declare-const x Int)
(declare-const y Int)
(assert (= x 2))
(assert (= y 1))
(assert (not false))
(check-sat)
(get-value (x y))
